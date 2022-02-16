all:
	$(MAKE) -C qbe-sml
	$(MAKE) -C qbe2c

clean:
	$(MAKE) -C qbe-sml clean
	$(MAKE) -C qbe2c clean
