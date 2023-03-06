all: lngen ott coq

coq: Exp_ott.v Exp_inf.v
	coqc Exp_ott.v
	coqc Exp_inf.v

Exp_inf.v: lngen
lngen: Exp.ott
	lngen --coq Exp_inf.v Exp.ott --coq-ott Exp_ott

Exp_all.tex: ott
Exp_ott.v: ott
ott: Exp.ott
	ott -i Exp.ott -o Exp_all.tex -o Exp_ott.v

.PHONY:
clean:
	rm *.aux *.vo *.vok *.vos *.glob
