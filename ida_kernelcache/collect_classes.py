#
# ida_kernelcache/collect_classes.py
# Brandon Azad
#
# Collects information about C++ classes in a kernelcache.
#

from collections import defaultdict

import idc
import idautils
import idaapi

import ida_utilities as idau
import classes
import segment
import vtable

_log = idau.make_log(1, __name__)

# IDK where IDA defines these.
_MEMOP_PREINDEX  = 0x20
_MEMOP_POSTINDEX = 0x80

_MEMOP_WBINDEX   = _MEMOP_PREINDEX | _MEMOP_POSTINDEX

# on 64bit devices __DATA_CONST segment is used for constant data
# instead of __DATA (eg __DATA_CONST.__const instead of __DATA.__const)
if idau.WORD_SIZE == 4:
    _CONST_SEGNAME = '__DATA'
else:
    _CONST_SEGNAME = '__DATA_CONST'

class _Regs(object):
    """A set of registers for _emulate_arm64/32."""

    class _Unknown:
        """A wrapper class indicating that the value is unknown."""
        def __add__(self, other):
            return _Regs.Unknown
        def __radd__(self, other):
            return _Regs.Unknown
        def __nonzero__(self):
            return False

    _reg_names = idautils.GetRegisterList()
    Unknown = _Unknown()

    def __init__(self):
        self.clearall()

    def clearall(self):
        self._regs = {}

    def clear(self, reg):
        try:
            del self._regs[self._reg(reg)]
        except KeyError:
            pass

    def _reg(self, reg):
        if isinstance(reg, (int, long)):
            reg = _Regs._reg_names[reg]

        # Automatically map Rn to Xn
        if reg[0] == 'R' and reg[1:].isdigit():
            reg = 'X' + reg[1:]

        return reg

    def __getitem__(self, reg):
        try:
            return self._regs[self._reg(reg)]
        except:
            return _Regs.Unknown

    def __setitem__(self, reg, value):
        if value is None or value is _Regs.Unknown:
            self.clear(self._reg(reg))
        else:
            self._regs[self._reg(reg)] = value & 0xffffffffffffffff

def _emulate_arm64(start, end=None, count=None, on_BL=None, on_RET=None):
    """A very basic partial Arm64 emulator that does just enough to find OSMetaClass
    information."""
    # Super basic emulation.
    reg = _Regs()
    def load(addr, dtyp):
        if not addr:
            return None
        if dtyp == idaapi.dt_qword:
            size = 8
        elif dtyp == idaapi.dt_dword:
            size = 4
        else:
            return None
        return idau.read_word(addr, size)
    def cleartemps():
        for t in ['X{}'.format(i) for i in range(0, 19)]:
            reg.clear(t)
    for insn in idau.Instructions(start, end=end, count=count):
        mnem = insn.get_canon_mnem()
        if mnem == 'ADRP' or mnem == 'ADR':
            reg[insn.Op1.reg] = insn.Op2.value
        elif mnem == 'ADD' and insn.Op2.type == idc.o_reg and insn.Op3.type == idc.o_imm:
            reg[insn.Op1.reg] = reg[insn.Op2.reg] + insn.Op3.value
        elif mnem == 'NOP':
            pass
        elif mnem == 'MOV' and insn.Op2.type == idc.o_imm:
            reg[insn.Op1.reg] = insn.Op2.value
        elif mnem == 'MOV' and insn.Op2.type == idc.o_reg:
            reg[insn.Op1.reg] = reg[insn.Op2.reg]
        elif mnem == 'RET':
            if on_RET:
                on_RET(reg)
            break
        elif (mnem == 'STP' or mnem == 'LDP') and insn.Op3.type == idc.o_displ:
            if insn.auxpref & _MEMOP_WBINDEX:
                reg[insn.Op3.reg] = reg[insn.Op3.reg] + insn.Op3.addr
            if mnem == 'LDP':
                reg.clear(insn.Op1.reg)
                reg.clear(insn.Op2.reg)
        elif (mnem == 'STR' or mnem == 'LDR') and not insn.auxpref & _MEMOP_WBINDEX:
            if mnem == 'LDR':
                if insn.Op2.type == idc.o_displ:
                    reg[insn.Op1.reg] = load(reg[insn.Op2.reg] + insn.Op2.addr, insn.Op1.dtyp)
                else:
                    reg.clear(insn.Op1.reg)
        elif mnem == 'BL' and insn.Op1.type == idc.o_near:
            if on_BL:
                on_BL(insn.Op1.addr, reg)
            cleartemps()
        else:
            _log(10, 'Unrecognized instruction at address {:#x}', insn.ea)
            reg.clearall()

def _emulate_arm32(start, end=None, count=None, on_BL=None, on_RET=None):
    """A very basic partial Arm32 emulator that does just enough to find OSMetaClass
    information."""
    # Super basic emulation.
    reg = _Regs()
    def load(addr, dtyp):
        if not addr:
            return None
        if dtyp == idaapi.dt_dword:
            size = 4
        else:
            return None
        return idau.read_word(addr, size)
    def cleartemps():
        for t in ['R{}'.format(i) for i in range(0, 12)]:
            reg.clear(t)

    # Handle thumb stuff
    start = start & ~1
    if end is not None:
        end = (end + 1) & ~1

    # if bl is found, lr is replaced, and marked dirty
    # if pop {... lr ...} is found, lr is assumed to be restored to
    # original, "clean" state
    lr_dirty = False

    # Special registers have special handling
    _SP_REG = 13
    _LR_REG = 14
    _PC_REG = 15

    for insn in idau.Instructions(start, end=end, count=count):
        mnem = insn.get_canon_mnem()
        _log(12, 'Regs: {}', reg._regs)
        _log(11, 'Processing instruction {} at {:#x}', mnem, insn.ea)
        if mnem == 'ADR':
            reg[insn.Op1.reg] = insn.Op2.value
        elif ((mnem == 'ADD' or mnem == 'SUB')
                and insn.Op1.type == insn.Op2.type == idc.o_reg
                and insn.Op1.reg == insn.Op2.reg == _SP_REG):
            # ignore add/sub on on SP
            pass
        elif mnem in ('ADD', 'ORR', 'SUB') and insn.Op2.type == idc.o_reg and insn.Op3.type == idc.o_imm:
            # There might be more operations, but in practice
            # add/sub/orr are enough

            # Don't bother checking if src register is unknown and
            # just mark dst register as unknown too
            if isinstance(reg[insn.Op2.reg], _Regs._Unknown):
                reg.clear(insn.Op1.reg)
            else:
                tmp = reg[insn.Op2.reg]
                if mnem == 'ADD':
                    tmp += insn.Op3.value
                elif mnem == 'SUB':
                    tmp -= insn.Op3.value
                elif mnem == 'ORR':
                    tmp |= insn.Op3.value
                else:
                    pass
                reg[insn.Op1.reg] = tmp
        elif mnem == 'ADD' and insn.Op3.type == idaapi.o_void:
            # Don't bother checking if it's unknown
            if not isinstance(reg[insn.Op1.reg], _Regs._Unknown):
                if insn.Op2.type == idc.o_imm:
                    # ADD Rx, <imm>
                    reg[insn.Op1.reg] = reg[insn.Op1.reg] + insn.Op2.value
                elif insn.Op2.type == idc.o_reg and insn.Op2.reg == _PC_REG:
                    # ADD Rx, PC -- special handling
                    # On ARM PC is "address of current instruction + 4"
                    # for historical reasons
                    reg[insn.Op1.reg] = reg[insn.Op1.reg] + insn.ea + 4
        elif mnem == 'NOP':
            pass
        elif mnem == 'MOV' and insn.Op2.type == idc.o_imm:
            reg[insn.Op1.reg] = insn.Op2.value
        elif mnem == 'MOV' and insn.Op2.type == idc.o_reg:
            reg[insn.Op1.reg] = reg[insn.Op2.reg]
        elif mnem == 'BX' and insn.Op1.type == idc.o_reg and insn.Op1.reg == _LR_REG:
            # bx lr is often used for ret
            if on_RET:
                on_RET(reg)
            break
        elif mnem == 'POP' and insn.Op1.type in (idc.o_idpspec1, idc.o_reg):
            poped = []

            # Either it's one register pop'ped
            if insn.Op1.type == idc.o_reg:
                poped.append(insn.Op1.reg)

            # Or whole set of them, identified by specval bits
            if insn.Op1.type == idc.o_idpspec1:
                for i in range(0, 16):
                    if insn.Op1.specval & (1<<i):
                        poped.append(i)

            for i in poped:
                reg.clear(i)

            if _PC_REG in poped:
                # pop {...pc...} is another way for ret
                if on_RET:
                    on_RET(reg)
                break
            elif _LR_REG in poped:
                lr_dirty = False
        elif mnem == 'BL' and insn.Op1.type == idc.o_near:
            if on_BL:
                on_BL(insn.Op1.addr, reg)
            cleartemps()
            lr_dirty = True
        elif (mnem == 'B' and insn.Op1.type == idc.o_near) or (mnem in ('CBZ', 'CBNZ') and insn.Op2.type == idc.o_near):
            dest = insn.Op1.addr if insn.Op2.type == 0 else insn.Op2.addr
            if start <= dest <= end:
                # silently ignoring branch since start<=dest<=end
                # So we check all code not skipping anything because of
                # conditions, and also don't get stuck in a loop
                continue

            if not lr_dirty:
                # special case -- when first instruction is branch to
                # another place -- means that current function is stub
                if insn.ea == start:
                    _log(11, 'Following {} at {:#x} (to {:#x})', mnem, insn.ea, dest)
                    _emulate_arm(dest, idc.FindFuncEnd(dest), on_BL=on_BL, on_RET=on_RET, reg=reg)
                elif on_RET:
                    # Consider as bl & ret -- usually happens as a way
                    # of optimization, when return func2() in the end of
                    # func1 is replaced by "b _func2"
                    if on_BL:
                        on_BL(dest, reg)
                        cleartemps()
                    if on_RET:
                        on_RET(reg)
            else:
                _log(11, 'NOT Following {} at {:#x} (to {:#x}) and not considering as ret', mnem, insn.ea, dest)
            break
        elif mnem == 'LDR' and insn.Op2.type == idc.o_mem:
            # LDR Rx, =ADDR
            reg[insn.Op1.reg] = load(insn.Op2.addr, insn.Op1.dtype)
        elif mnem == 'LDR' and insn.Op2.type == idc.o_displ and insn.Op2.value == 0:
            # LDR Rx, [Ry]
            reg[insn.Op1.reg] = load(reg[insn.Op2.reg], insn.Op1.dtype)
        elif mnem == 'PUSH' or mnem == 'STR':
            # They don't affect registers directly
            pass
        else:
            # silently clear on V instructions -- they're used pretty
            # often but aren't needed for OSMetaClass stuff
            if mnem not in ('VMOV', 'VST1', 'VLD1'):
                _log(6, 'Unrecognized instruction {} at address {:#x}', mnem, insn.ea)
            reg.clearall()

# Universal function
if idau.WORD_SIZE == 4:
    _emulate_arm = _emulate_arm32
else: # == 8
    _emulate_arm = _emulate_arm64


class _OneToOneMapFactory(object):
    """A factory to extract the largest one-to-one submap."""

    def __init__(self):
        self._as_to_bs = defaultdict(set)
        self._bs_to_as = defaultdict(set)

    def add_link(self, a, b):
        """Add a link between the two objects."""
        self._as_to_bs[a].add(b)
        self._bs_to_as[b].add(a)

    def _make_unique_oneway(self, xs_to_ys, ys_to_xs, bad_x=None):
        """Internal helper to make one direction unique."""
        for x, ys in xs_to_ys.items():
            if len(ys) != 1:
                if bad_x:
                    bad_x(x, ys)
                del xs_to_ys[x]
                for y in ys:
                    del ys_to_xs[y]

    def _build_oneway(self, xs_to_ys):
        """Build a one-way mapping after pruning."""
        x_to_y = dict()
        for x, ys in xs_to_ys.items():
            x_to_y[x] = next(iter(ys))
        return x_to_y

    def build(self, bad_a=None, bad_b=None):
        """Extract the smallest one-to-one submap."""
        as_to_bs = dict(self._as_to_bs)
        bs_to_as = dict(self._bs_to_as)
        self._make_unique_oneway(as_to_bs, bs_to_as, bad_a)
        self._make_unique_oneway(bs_to_as, as_to_bs, bad_b)
        return self._build_oneway(as_to_bs)

def _process_mod_init_func_for_metaclasses(func, found_metaclass):
    """Process a function from the __mod_init_func section for OSMetaClass information."""
    _log(4, 'Processing function {:#x} ({})', func, idc.GetFunctionName(func))
    def on_BL(addr, reg):
        X0, X1, X3 = reg['X0'], reg['X1'], reg['X3']
        if not (X0 and X1 and X3):
            return
        _log(5, 'Have call to {:#x}({:#x}, {:#x}, ?, {:#x})', addr, X0, X1, X3)
        # OSMetaClass::OSMetaClass(this, className, superclass, classSize)
        if not idc.SegName(X1).endswith("__TEXT.__cstring") or not idc.SegName(X0):
            return
        found_metaclass(X0, idc.GetString(X1), X3, reg['X2'] or None)
    _emulate_arm(func, idc.FindFuncEnd(func), on_BL=on_BL)

def _process_mod_init_func_section_for_metaclasses(segstart, found_metaclass):
    """Process a __mod_init_func section for OSMetaClass information."""
    segend = idc.SegEnd(segstart)
    for func in idau.ReadWords(segstart, segend):
        _process_mod_init_func_for_metaclasses(func, found_metaclass)

def _collect_metaclasses():
    """Collect OSMetaClass information from all kexts in the kernelcache."""
    # Collect associations from class names to metaclass instances and vice versa.
    metaclass_to_classname_builder = _OneToOneMapFactory()
    metaclass_to_class_size      = dict()
    metaclass_to_meta_superclass = dict()
    def found_metaclass(metaclass, classname, class_size, meta_superclass):
        metaclass_to_classname_builder.add_link(metaclass, classname)
        metaclass_to_class_size[metaclass]      = class_size
        metaclass_to_meta_superclass[metaclass] = meta_superclass
    for ea in idautils.Segments():
        segname = idc.SegName(ea)
        if not segname.endswith(_CONST_SEGNAME + '__mod_init_func'):
            continue
        _log(2, 'Processing segment {}', segname)
        _process_mod_init_func_section_for_metaclasses(ea, found_metaclass)
    # Filter out any class name (and its associated metaclasses) that has multiple metaclasses.
    # This can happen when multiple kexts define a class but only one gets loaded.
    def bad_classname(classname, metaclasses):
        _log(0, 'Class {} has multiple metaclasses: {}', classname,
                ', '.join(['{:#x}'.format(mc) for mc in metaclasses]))
    # Filter out any metaclass (and its associated class names) that has multiple class names. I
    # have no idea why this would happen.
    def bad_metaclass(metaclass, classnames):
        _log(0, 'Metaclass {:#x} has multiple classes: {}', metaclass,
                ', '.join(classnames))
    # Return the final dictionary of metaclass info.
    metaclass_to_classname = metaclass_to_classname_builder.build(bad_metaclass, bad_classname)
    metaclass_info = dict()
    for metaclass, classname in metaclass_to_classname.items():
        meta_superclass = metaclass_to_meta_superclass[metaclass]
        superclass_name = metaclass_to_classname.get(meta_superclass, None)
        metaclass_info[metaclass] = classes.ClassInfo(classname, metaclass, None, None,
                metaclass_to_class_size[metaclass], superclass_name, meta_superclass)
    return metaclass_info

_VTABLE_GETMETACLASS    = vtable.VTABLE_OFFSET + 7
_MAX_GETMETACLASS_INSNS = 3

def _get_vtable_metaclass(vtable_addr, metaclass_info):
    """Simulate the getMetaClass method of the vtable and check if it returns an OSMetaClass."""
    getMetaClass = idau.read_word(vtable_addr + _VTABLE_GETMETACLASS * idau.WORD_SIZE)
    def on_RET(reg):
        on_RET.ret = reg['X0']
    on_RET.ret = None

    # use count to avoid alignment errors on arm32
    _emulate_arm(getMetaClass, count=_MAX_GETMETACLASS_INSNS, on_RET=on_RET)
    if on_RET.ret in metaclass_info:
        return on_RET.ret

def _process_const_section_for_vtables(segstart, metaclass_info, found_vtable):
    """Process a __const section to search for virtual method tables."""
    segend = idc.SegEnd(segstart)
    addr = segstart
    while addr < segend:
        possible, length = vtable.vtable_length(addr, segend, scan=True)
        if possible:
            metaclass = _get_vtable_metaclass(addr, metaclass_info)
            if metaclass:
                _log(4, 'Vtable at address {:#x} has metaclass {:#x}', addr, metaclass)
                found_vtable(metaclass, addr, length)
        addr += length * idau.WORD_SIZE

def _collect_vtables(metaclass_info):
    """Use OSMetaClass information to search for virtual method tables."""
    # Build a mapping from OSMetaClass instances to virtual method tables.
    metaclass_to_vtable_builder = _OneToOneMapFactory()
    vtable_lengths = {}
    def found_vtable(metaclass, vtable, length):
        vtable_lengths[vtable] = length
        if segment.kernelcache_kext(metaclass) == segment.kernelcache_kext(vtable):
            metaclass_to_vtable_builder.add_link(metaclass, vtable)
    for ea in idautils.Segments():
        segname = idc.SegName(ea)
        if not segname.endswith(_CONST_SEGNAME + '.__const'):
            continue
        _log(2, 'Processing segment {}', segname)
        _process_const_section_for_vtables(ea, metaclass_info, found_vtable)
    # If a metaclass has multiple vtables, that's really weird, unless the metaclass is
    # OSMetaClass's metaclass. In that case all OSMetaClass subclasses will have their vtables
    # refer back to OSMetaClass's metaclass.
    # TODO: Right now we don't do anything special for this case.
    def bad_metaclass(metaclass, vtables):
        vtinfo = ['{:#x}'.format(vt) for vt in vtables]
        _log(0, 'Metaclass {:#x} ({}) has multiple vtables: {}', metaclass,
                metaclass_info[metaclass].classname, ', '.join(vtinfo))
    # If a vtable has multiple metaclasses, that's really weird.
    def bad_vtable(vtable, metaclasses):
        mcinfo = ['{:#x} ({})'.format(mc, metaclass_info[mc].classname) for mc in metaclasses]
        _log(0, 'Vtable {:#x} has multiple metaclasses: {}', vtable, ', '.join(mcinfo))
    metaclass_to_vtable = metaclass_to_vtable_builder.build(bad_metaclass, bad_vtable)
    # Print a list of the metaclasses that have been eliminated.
    if _log(1):
        original  = set(metaclass_info.keys())
        remaining = set(metaclass_to_vtable.keys())
        _log(1, 'Eliminated classes:')
        for metaclass in original.difference(remaining):
            _log(1, '\t{:#x}  {}', metaclass, metaclass_info[metaclass].classname)
    # The resulting mapping may have fewer metaclasses than metaclass_info.
    class_info = dict()
    for metaclass, vtable in metaclass_to_vtable.items():
        classinfo = metaclass_info[metaclass]
        # Add the vtable and its length, which we didn't have earlier.
        classinfo.vtable        = vtable
        classinfo.vtable_length = vtable_lengths[vtable]
        # If this class's superclass is still live, set its superclass field and add ourselves to
        # the superclass's children. This is safe since this is the last filtering operation.
        if classinfo.meta_superclass in metaclass_to_vtable:
            classinfo.superclass = metaclass_info[classinfo.meta_superclass]
            classinfo.superclass.subclasses.add(classinfo)
        class_info[classinfo.classname] = classinfo
    return class_info, vtable_lengths

def _check_filetype(filetype):
    """Checks that the filetype is compatible before trying to process it."""
    return 'Mach-O' in filetype and 'ARM' in filetype

def collect_class_info_internal():
    """Collect information about C++ classes defined in a kernelcache.

    Arm64 only.
    """
    filetype = idaapi.get_file_type_name()
    if not _check_filetype(filetype):
        _log(-1, 'Bad file type "{}"', filetype)
        return None
    _log(1, 'Collecting information about OSMetaClass instances')
    metaclass_info = _collect_metaclasses()
    if not metaclass_info:
        _log(-1, 'Could not collect OSMetaClass instances')
        return None
    _log(1, 'Searching for virtual method tables')
    class_info, all_vtables = _collect_vtables(metaclass_info)
    if not class_info:
        _log(-1, 'Could not collect virtual method tables')
        return None
    _log(1, 'Done')
    return class_info, all_vtables

