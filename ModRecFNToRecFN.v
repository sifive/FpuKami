Require Import Definitions Round String Kami.Syntax.

Section RecFN_to_RecFN.
  Variable name: string.
  Variable expWidthMinus2 sigWidthMinus2: nat.
  Variable out_expWidthMinus2 out_sigWidthMinus2: nat.
  Local Notation "^ x" := (name ++ "#" ++ x)%string (at level 100).

  Open Scope kami_expr.
  
  Definition RecFNToRecFN_module :=
    MODULE {
        Rule ^"RecFNToRecFN" :=
          Call input: RecFN expWidthMinus2 sigWidthMinus2  <- "input" ();
          Call tiny: Bool <- "tiny" ();
          Call roundMode: Bit 3 <- "roundMode" ();
          LET inputNF <- getNF_from_RecFN #input; 
          Call "input_NF" (#inputNF : NF expWidthMinus2 sigWidthMinus2);
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
          Call "output_NF" ((#roundOutput @% "out") : NF out_expWidthMinus2 out_sigWidthMinus2);
          Call "output_NF_sig" ((#roundOutput @% "out") @% "sig": Bit (out_sigWidthMinus2 + 1));
          Call "output_subnormalExp" (isSubnormalExp (#roundOutput @% "out") : Bool);
          Call "output_specializedFrac" (specializedFrac (#roundOutput @% "out"): Bit (out_sigWidthMinus2 + 1));
          Call "output_nonSpecializedFrac" (nonSpecializedFrac (#roundOutput @% "out"): Bit (out_sigWidthMinus2 + 1));
          Call "outputRecFN" (getRecFN_from_NF(#roundOutput @% "out"): RecFN out_expWidthMinus2 out_sigWidthMinus2);
          Call "output_flags" ((#roundOutput @% "exceptionFlags"): _);
 
        Retv
      }.
  Close Scope kami_expr.

End RecFN_to_RecFN.

Definition RecF16ToRecF32 := RecFNToRecFN_module "fpu" 6 6 6 22.
Definition RecF16ToRecF64 := RecFNToRecFN_module "fpu" 6 6 9 51.
Definition RecF32ToRecF64 := RecFNToRecFN_module "fpu" 6 22 9 51.
Definition RecF32ToRecF16 := RecFNToRecFN_module "fpu" 6 22 6 6.
Definition RecF64ToRecF32 := RecFNToRecFN_module "fpu" 9 51 6 22.
Definition RecF64ToRecF16 := RecFNToRecFN_module "fpu" 9 51 6 6.
