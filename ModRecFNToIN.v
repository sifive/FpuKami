Require Import FpuKami.Definitions FpuKami.NFToIN String Kami.AllNotations FpuKami.Round.
Section FNToIN.
  Variable name: string.
  Variable szMinus2: nat.
  Variable expWidthMinus2 sigWidthMinus2: nat.
  Local Notation "^ x" := (name ++ "#" ++ x)%string (at level 100).
  Local Notation sz := (szMinus2 + 1 + 1).

  Variable expWidth_prop: expWidthMinus2 >= 2.
  Variable expWidthMinus2_plus4_gt_sigWidth: pow2 expWidthMinus2 + 4 > (sigWidthMinus2 + 1 + 1).

  Open Scope kami_expr.
  Definition RecFNToINMod :=
    MODULE {
        Rule ^"RecINToFN" :=
          Call inputFN: RecFN expWidthMinus2 sigWidthMinus2  <- "inputFN" ();

          Call signedOut: Bool <- "signedOut" ();
          Call roundMode: Bit 3 <- "roundMode" ();
          LET inputNF<- getNF_from_RecFN #inputFN;

          LET NFToINInput: NFToINInput expWidthMinus2 sigWidthMinus2 <-
                                       STRUCT {
                                         "inNF" ::= #inputNF;
                                         "roundingMode" ::= #roundMode;
                                         "signedOut" ::= #signedOut
                                       };
          LETA NFToIN : NFToINOutput szMinus2 <-
                                NFToIN_action szMinus2 expWidth_prop expWidthMinus2_plus4_gt_sigWidth #NFToINInput;
          
          Call "exceptionFlags" (#NFToIN @% "flags": _) ;
          Call "outputIN" (#NFToIN @% "outIN": _);
        Retv
      }.
  Close Scope kami_expr.

End FNToIN.

Definition RecF32ToI32 := @RecFNToINMod "fpu" 30 6 22 ltac:(lia) ltac:(simpl;lia).
Definition RecF32ToI64 := @RecFNToINMod "fpu" 62 6 22 ltac:(lia) ltac:(simpl;lia).
Definition RecF64ToI32 := @RecFNToINMod "fpu" 30 9 51 ltac:(lia) ltac:(simpl;lia).
Definition RecF64ToI64 := @RecFNToINMod "fpu" 62 9 51 ltac:(lia) ltac:(simpl;lia).
Definition RecF16ToI32 := @RecFNToINMod "fpu" 30 6 6 ltac:(lia) ltac:(simpl;lia).
Definition RecF16ToI64 := @RecFNToINMod "fpu" 62 6 6 ltac:(lia) ltac:(simpl;lia).
