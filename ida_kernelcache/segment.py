#
# ida_kernelcache/segment.py
# Brandon Azad
#
# Functions for interacting with the segments of the kernelcache in IDA. No prior initialization is
# necessary.
#

import idc

import ida_utilities as idau
import kernel

_log = idau.make_log(0, __name__)


_LOAD_COMMAND = 'load_command'

if idau.WORD_SIZE == 4:
    _MACH_HEADER = 'mach_header'
    _SEGMENT_COMMAND = 'segment_command'
    _SECTION = 'section'
    _LC_SEGMENT = 0x1
else: # idau.WORD_SIZE == 8
    _MACH_HEADER = 'mach_header_64'
    _SEGMENT_COMMAND = 'segment_command_64'
    _SECTION = 'section_64'
    _LC_SEGMENT = 0x19

idc.Til2Idb(-1, _MACH_HEADER)
idc.Til2Idb(-1, _LOAD_COMMAND)
idc.Til2Idb(-1, _SEGMENT_COMMAND)
idc.Til2Idb(-1, _SECTION)

def _macho_segments_and_sections(ea):
    """A generator to iterate through a Mach-O file's segments and sections.

    Each iteration yields a tuple:
        (segname, segstart, segend, [(sectname, sectstart, sectend), ...])
    """
    hdr   = idau.read_struct(ea, _MACH_HEADER, asobject=True)
    nlc   = hdr.ncmds
    lc    = int(hdr) + len(hdr)
    lcend = lc + hdr.sizeofcmds
    while lc < lcend and nlc > 0:
        loadcmd = idau.read_struct(lc, _LOAD_COMMAND, asobject=True)
        if loadcmd.cmd == _LC_SEGMENT:
            segcmd = idau.read_struct(lc, _SEGMENT_COMMAND, asobject=True)
            segname  = idau.null_terminated(segcmd.segname)
            segstart = segcmd.vmaddr
            segend   = segstart + segcmd.vmsize
            sects    = []
            sc  = int(segcmd) + len(segcmd)
            for i in range(segcmd.nsects):
                sect = idau.read_struct(sc, _SECTION, asobject=True)
                sectname  = idau.null_terminated(sect.sectname)
                sectstart = sect.addr
                sectend   = sectstart + sect.size
                sects.append((sectname, sectstart, sectend))
                sc += len(sect)
            yield (segname, segstart, segend, sects)
        lc  += loadcmd.cmdsize
        nlc -= 1

def _initialize_segments_in_kext(kext, mach_header, skip=[]):
    """Rename the segments in the specified kext."""
    def log_seg(segname, segstart, segend):
        _log(3, '+ segment {: <20} {:x} - {:x}  ({:x})', segname, segstart, segend,
            segend - segstart)
    def log_sect(sectname, sectstart, sectend):
        _log(3, '  section {: <20} {:x} - {:x}  ({:x})', sectname, sectstart, sectend,
                sectend - sectstart)
    def log_gap(gapno, start, end, mapped):
        mapped = 'mapped' if mapped else 'unmapped'
        _log(3, '  gap     {: <20} {:x} - {:x}  ({:x}, {})', gapno, start, end,
            end - start, mapped)
    def process_region(segname, name, start, end):
        assert end >= start
        if segname in skip:
            _log(2, 'Skipping segment {}', segname)
            return
        newname = '{}.{}'.format(segname, name)
        if kext:
            newname = '{}:{}'.format(kext, newname)
        if start == end:
            _log(2, 'Skipping empty region {} at {:x}', newname, start)
            return
        ida_segstart = idc.SegStart(start)
        if ida_segstart == idc.BADADDR:
            _log(0, "IDA doesn't think this is a real segment: {:x} - {:x}", start, end)
            return
        ida_segend = idc.SegEnd(ida_segstart)
        if start != ida_segstart or end != ida_segend:
            _log(0, 'IDA thinks segment {} {:x} - {:x} should be {:x} - {:x}', newname, start, end,
                    ida_segstart, ida_segend)
            return
        _log(2, 'Rename {:x} - {:x}: {} -> {}', start, end, idc.SegName(start), newname)
        idc.SegRename(start, newname)
    def process_gap(segname, gapno, start, end):
        mapped = idau.is_mapped(start)
        log_gap(gapno, start, end, mapped)
        if mapped:
            name = 'HEADER' if start == mach_header else '__gap_' + str(gapno)
            process_region(segname, name, start, end)
    for segname, segstart, segend, sects in _macho_segments_and_sections(mach_header):
        log_seg(segname, segstart, segend)
        lastend = segstart
        gapno   = 0
        for sectname, sectstart, sectend in sects:
            if lastend < sectstart:
                process_gap(segname, gapno, lastend, sectstart)
                gapno += 1
            log_sect(sectname, sectstart, sectend)
            process_region(segname, sectname, sectstart, sectend)
            lastend = sectend
        if lastend < segend:
            process_gap(segname, gapno, lastend, segend)
            gapno += 1

def initialize_segments():
    """Rename the kernelcache segments in IDA according to the __PRELINK_INFO data.

    Rename the kernelcache segments based on the contents of the __PRELINK_INFO dictionary.
    Segments are renamed according to the scheme '[<kext>:]<segment>.<section>', where '<kext>' is
    the bundle identifier if the segment is part of a kernel extension. The special region
    containing the Mach-O header is renamed '[<kext>:]<segment>.HEADER'.
    """
    # First rename the kernel segments.
    _log(1, 'Renaming kernel segments')
    kernel_skip = ['__PRELINK_TEXT', '__PLK_TEXT_EXEC', '__PRELINK_DATA', '__PLK_DATA_CONST']
    _initialize_segments_in_kext(None, kernel.base, skip=kernel_skip)
    # Process each kext identified by the __PRELINK_INFO.
    prelink_info_dicts = kernel.prelink_info['_PrelinkInfoDictionary']
    for kext_prelink_info in prelink_info_dicts:
        kext = kext_prelink_info.get('CFBundleIdentifier', None)
        mach_header = kext_prelink_info.get('_PrelinkExecutableLoadAddr', None)
        if kext is not None and mach_header is not None:
            orig_kext = idc.SegName(mach_header).split(':', 1)[0]
            if '.kpi.' not in kext and orig_kext != kext:
                _log(0, 'Renaming kext {} -> {}', orig_kext, kext)
            _log(1, 'Renaming segments in {}', kext)
            _initialize_segments_in_kext(kext, mach_header)

def kernelcache_kext(ea):
    """Return the name of the kext to which the given linear address belongs.

    Only works if segments have been renamed using initialize_segments().
    """
    name = idc.SegName(ea) or ''
    if ':' in name:
        return idc.SegName(ea).split(':', 1)[0]
    return None

