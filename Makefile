check:
	coqc -Q . '' Jech.v
	find purgatorium/ -type f -name '*.v' -exec echo 'Skipping {}' \;

	coqc -Q . '' Jech.v
	find purgatorium/ -name '*.v' -exec echo 'Skipping {}' ;
