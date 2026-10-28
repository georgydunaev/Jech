check:
	coqc -Q . '' Jech.v

.PHONY: check

# Exclude purgatorium files
purgatorium/%:
	@echo "Skipping purgatorium file: $@"
	@: