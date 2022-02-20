bin/qbe2c: qbe2c | bin
	cp qbe2c/qbe2c $@

qbe2c:
	$(MAKE) -C qbe-sml
	$(MAKE) -C qbe2c

bin:
	mkdir bin

clean:
	$(MAKE) -C qbe-sml clean
	$(MAKE) -C qbe2c clean
	rm -rf bin

.PHONY: qbe2c clean
