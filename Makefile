check:
	coqc -Q . '' Jech.v
	coqc -Q . '' Part_III.v
	coqc -Q . '' section_mostowski.v
	find purgatorium/ -type f -name '*.v' -exec echo 'Skipping {}' \;
