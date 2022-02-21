qbe2c:
	$(MAKE) -C qbe-sml
	$(MAKE) -C qbe2c

clean:
	$(MAKE) -C qbe-sml clean
	rm -rf bin

.PHONY: qbe2c clean
