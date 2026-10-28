# Automatically created by mistral/mistral-small-latest (Capability Tier 2)

check:
	docker run --rm -v $(PWD):/work -w /work coqorg/coq coqc -Q . '' Jech.v
