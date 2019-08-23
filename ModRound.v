Require Import Kami.AllNotations FpuKami.Definitions FpuKami.Round String.
Require Export Nat.

Section FpuConvert2.
  Variable name: string.
  Variable expWidthMinus2 sigWidthMinus2: nat.
  Variable out_expWidthMinus2 out_sigWidthMinus2: nat.
  Local Notation "^ x" := (name ++ "#" ++ x)%string (at level 100).

  Open Scope kami_expr.
  Definition NF_from_FN :=
    MODULE {
        Rule ^"NF_from_FN" :=
          Call input: FN expWidthMinus2 sigWidthMinus2  <- "input" ();
          Call tiny: Bool <- "tiny" ();
          Call roundMode: Bit 3 <- "roundMode" ();
          LET inputNF <- getNF_from_FN #input;
          LET roundInput: RoundInput _ _ <-
                                             STRUCT {
                                               "in" ::= #inputNF;
                                               "afterRounding" ::= #tiny;
                                               "roundingMode" ::= #roundMode
                                             };


          LETA roundOutput <- (RoundNF_action out_expWidthMinus2 out_sigWidthMinus2
                                              (pow2 (out_expWidthMinus2 + 1) - 2)%nat
                                              (pow2 (out_expWidthMinus2 + 1) + (out_sigWidthMinus2 + 1) - 2)%nat
                                              (pow2 (out_expWidthMinus2 + 1) - 1)%nat
                                              #roundInput);

          Call "exceptionFlags" (#roundOutput @% "exceptionFlags": _) ;
          Call "outputFN" (((#roundOutput @% "out")): _);
        Retv
      }.
  Close Scope kami_expr.

End FpuConvert2.

