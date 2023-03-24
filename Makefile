EXP_FOLDER = Exp

all: ott lngen adjust coq

coq: Exp_ott.v Exp_inf.v
	coqc -Q . Exp Exp_ott.v
	coqc -Q . Exp Exp_inf.v

adjust: Exp_inf.v
	sed -i".original" -e /Require\ Export\ Exp/s/^/From\ Exp\ / Exp_inf.v

Exp_inf.v: lngen
lngen: Exp.ott
	lngen --coq Exp_inf.v Exp.ott --coq-ott Exp_ott --coq-admit

Exp_all.tex: ott
# Exp_ott.v: ott
ott: Exp.ott
	ott -i Exp.ott -o Exp_ott.v -coq_lngen true -coq_expand_list_types true
	ott -i Exp.ott -o Exp_all.tex

.PHONY:
clean:
	rm -f .*.aux *.vo *.vok *.vos *.glob
