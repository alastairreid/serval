
# build a test binary
test.o: test.c
	aarch64-none-elf-cc test.c  -c -g

# another test binary
ELF = ../asl-interpreter/tests/test_O2.elf
DIR = serval/arm

$(DIR)/test.map.rkt: $(ELF)
	(echo "#lang reader serval/lang/nm" ; nm $^) > $@

$(DIR)/test.globals.rkt: $(ELF)
	(echo "#lang reader serval/lang/dwarf" ; aarch64-none-elf-objdump --dwarf=info $^) > $@

$(DIR)/test.binary.rkt: $(ELF)
	serval/lang/elf_loader.py $^ > $@

symbols:: $(DIR)/test.map.rkt $(DIR)/test.globals.rkt $(DIR)/test.binary.rkt

clean::
	$(RM) $(DIR)/test.map.rkt $(DIR)/test.globals.rkt $(DIR)/test.binary.rkt
