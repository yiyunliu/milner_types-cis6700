EXP_FOLDER = Exp

all: ott lngen adjust coq

coq: $(EXP_FOLDER)/Exp_ott.v $(EXP_FOLDER)/Exp_inf.v
	coqc -Q . $(EXP_FOLDER) $(EXP_FOLDER)/Exp_ott.v
	coqc -Q . $(EXP_FOLDER) $(EXP_FOLDER)/Exp_inf.v

adjust: $(EXP_FOLDER)/Exp_inf.v
	sed -i".original" -e /Require\ Export\ $(EXP_FOLDER)/s/^/From\ $(EXP_FOLDER)\ / $(EXP_FOLDER)/Exp_inf.v

$(EXP_FOLDER)/Exp_inf.v: lngen
lngen: Exp.ott
	lngen --coq $(EXP_FOLDER)/Exp_inf.v Exp.ott --coq-ott Exp_ott

Exp_all.tex: ott
$(EXP_FOLDER)/Exp_ott.v: ott
ott: Exp.ott
	ott -i Exp.ott -o $(EXP_FOLDER)/Exp_all.tex -o $(EXP_FOLDER)/Exp_ott.v

.PHONY:
clean:
	cd $(EXP_FOLDER) && rm *.aux *.vo *.vok *.vos *.glob
