check:
	coqc -Q . '' Jech.v
	find purgatorium/ -name '*.v' -exec echo 'Skipping {}' ;
