all: lngen ott

coq: Exp/Exp_ott.v Exp/Exp_inf.v
	coqc Exp/Exp_ott.v
	coqc Exp/Exp_inf.v

Exp_inf.v: lngen
lngen: Exp.ott
	lngen --coq Exp/Exp_inf.v Exp.ott

Exp_all.tex: ott
Exp_ott.v: ott
ott: Exp.ott
	ott -i Exp.ott -o Exp/Exp_all.tex -o Exp/Exp_ott.v

.PHONY:
clean:
	cd Exp && rm *.aux *.vo *.vok *.vos *.glob
