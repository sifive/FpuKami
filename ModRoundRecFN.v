Require Import Definitions String Kami.Syntax Round.

Section Round.
  Variable expWidthMinus2 sigWidthMinus2: nat.
  Variable out_expWidthMinus2 out_sigWidthMinus2: nat.

  Local Open Scope kami_expr.
  Definition RoundRecFN :=
    MODULE {
        Rule "RoundRecFN" :=
          Call roundInp: RoundInput expWidthMinus2 sigWidthMinus2 <- "roundInput"();
          Call invalidExc: Bool <- "invalidExc"();
          Call infiniteExc: Bool <- "infiniteExc"();
          LETA finalVal : RoundRecFN out_expWidthMinus2 out_sigWidthMinus2 <-
                                     convertLetExprSyntax_ActionT (RoundNF_to_RecFN_def_expr _ _ #roundInp #invalidExc #infiniteExc);
          Call "finalVal"(#finalVal: _);
          Retv
      }.
  Local Close Scope kami_expr.
End Round.

Definition RoundRecF16 := RoundRecFN 3 12 3 9.
Definition RoundRecF32 := RoundRecFN 6 25 6 22.
Definition RoundRecF64 := RoundRecFN 9 54 9 51.
