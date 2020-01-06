#! /usr/bin/env python3

'''
This converts an executable ELF file to a Racket file.

It would probably be better written in Racket - but, alas, my
Racket skills are not up to the task...
'''

import argparse
import re
import subprocess

parser = argparse.ArgumentParser(description='Convert ELF executable to Scheme')
parser.add_argument('elf', metavar='N', type=str, help='ELF executable file')
args = parser.parse_args()

header = subprocess.run(['aarch64-none-elf-readelf', '--program-headers', args.elf], stdout=subprocess.PIPE)
header = header.stdout.decode('utf-8').splitlines()

print('''
#lang rosette
(provide (all-defined-out))
''')

entry = None
segments = []
i = 0
while i < len(header)-1:
    m = re.match(r'\s*Entry point 0[xX]([0-9A-Fa-f]+)', header[i])
    if m:
        entry = int(m[1], 16)
        # print(f"Entry {entry:#0x}")
        print(f"(define entry #x{entry:02x})")

    m1 = re.match(r'\s*LOAD\s+0[xX]([0-9A-Fa-f]+)\s+0[xX]([0-9A-Fa-f]+)\s+0[xX]([0-9A-Fa-f]+)\s*$', header[i])
    m2 = re.match(r'\s+0[xX]([0-9A-Fa-f]+)\s+0[xX]([0-9A-Fa-f]+)\s+', header[i+1])
    if m1 and m2:
        offset = int(m1[1], 16)
        vaddr  = int(m1[2], 16)
        paddr  = int(m1[3], 16)
        fsize  = int(m2[1], 16)
        msize  = int(m2[2], 16)
        segments.append((offset, vaddr, paddr, fsize, msize))

    i = i+1

file = open(args.elf, mode='rb')
contents = file.read()
file.close()

for (offset, vaddr, paddr, fsize, msize) in segments:
    # print(f"LOAD {offset:#0x} {vaddr:#0x} {paddr:#0x} {fsize:#0x} {msize:#0x}")
    data = contents[offset : offset+fsize]
    if fsize < msize:
        data = data + '\x00' * (msize - fsize)
    # print(data)
    print('(define binary #hash(')
    for o in range(0, len(data), 4):
        w = int.from_bytes(data[o:o+4], byteorder='little')
        print(f"\t(#x{paddr+o:016x} . #x{w:08x})")
    print('))')
