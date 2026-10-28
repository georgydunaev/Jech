# Automatically created by groq/qwen/qwen3.8-27b (Capability Tier 2)

check:
	coqc -Q . '' Jech.v

check:
	docker run --rm -v $(PWD):/work -w /work coqorg/coq coqc -Q . '' Jech.v
