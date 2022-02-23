qbe2c: | bin
	$(MAKE) -C qbe-sml
	$(MAKE) -C qbe2c

bin:
	mkdir bin

clean:
	$(MAKE) -C qbe-sml clean
	rm -rf bin

.PHONY: qbe2c clean
