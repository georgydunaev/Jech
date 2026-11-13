check:
	coqc -Q . '' Jech.v
	coqc -Q . '' Part_III.v
	find purgatorium/ -type f -name '*.v' -exec echo 'Skipping {}' \;

