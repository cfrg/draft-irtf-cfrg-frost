TESTVECTORS := "frost-ed25519-sha512.json" "frost-ed448-shake256.json" "frost-ristretto255-sha512.json" "frost-p256-sha256.json" "frost-secp256k1-sha256.json"
FORMATTEDVECTORS := "test-vectors.txt"
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
	@python3 format_test_vectors.py $(TESTVECTORS) > $(FORMATTEDVECTORS)

.PHONY: clean
clean:
	rm -rf sagelib *.pyc *.sage.py *.log __pycache__ $(TESTVECTORS) $(FORMATTEDVECTORS)