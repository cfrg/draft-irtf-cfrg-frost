TESTVECTORS := "test-vectors"
SAGEFILES := $(basename $(notdir $(wildcard *.sage)))
PYFILES := $(addprefix sagelib/, $(addsuffix .py,$(SAGEFILES)))
.PRECIOUS: $(PYFILES)

.PHONY: pyfiles
pyfiles: sagelib/__init__.py $(PYFILES)

sagelib/__init__.py:
	mkdir -p sagelib
	echo pass > sagelib/__init__.py

sagelib/%.py: %.sage
	@echo "Parsing $<"
	@sage --preparse $<
	@mv $<.py $@

test: pyfiles
	@sage frost.sage

vectors: test
	@sage frost.sage > $(TESTVECTORS).json
	@python3 format_test_vectors.py $(TESTVECTORS).json > $(TESTVECTORS).txt

.PHONY: clean
clean:
	rm -rf sagelib *.pyc *.sage.py *.log __pycache__