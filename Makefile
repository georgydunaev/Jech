check:
	coqc -Q . '' Jech.v
	coqc -Q . '' Part_III.v
	coqc -Q . '' section_mostowski.v
	coqc -Q . '' section_cumulative_hierarchy.v
	coqc -Q . '' section_choice.v
	find purgatorium/ -type f -name '*.v' -exec echo 'Skipping {}' \;
