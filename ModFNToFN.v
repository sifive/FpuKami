Require Import Definitions Round String Kami.Syntax.

Section FN_to_FN.
  Variable name: string.
  Variable expWidthMinus2 sigWidthMinus2: nat.
  Variable out_expWidthMinus2 out_sigWidthMinus2: nat.
  Local Notation "^ x" := (name ++ "#" ++ x)%string (at level 100).

  Open Scope kami_expr.
  
  Definition FNToFN_module :=
    MODULE {
        Rule ^"FNToFN" :=
          Call input: FN expWidthMinus2 sigWidthMinus2  <- "input" ();
          Call tiny: Bool <- "tiny" ();
          Call roundMode: Bit 3 <- "roundMode" ();
          LET inputNF <- getNF_from_FN #input; 
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
          Call "output_NF_exp" ((#roundOutput @% "out") @% "sExp": _);
          Call "output_NF_isZero" ((#roundOutput @% "out") @% "isZero": _);
          Call "output_truncFrac" (truncFrac (#roundOutput @% "out") : _);
          Call "output_subnormalExp" (isSubnormalExp (#roundOutput @% "out") : Bool);
          Call "output_specializedFrac" (specializedFrac (#roundOutput @% "out"): Bit (out_sigWidthMinus2 + 1));
          Call "output_nonSpecializedFrac" (nonSpecializedFrac (#roundOutput @% "out"): Bit (out_sigWidthMinus2 + 1));
          Call "subNormDistFN" (subnormDist (#roundOutput@%"out"): _);
          Call "subNormFracFN" (subnormFrac (#roundOutput@%"out"): _);
          Call "specializedFracFN" (specializedFrac (#roundOutput@%"out"): _);
          Call "output" (getFN_from_NF(#roundOutput @% "out"): FN out_expWidthMinus2 out_sigWidthMinus2);
          Call "output_flags" ((#roundOutput @% "exceptionFlags"): _);
 
        Retv
      }.
  Close Scope kami_expr.

End FN_to_FN.

Definition F16ToF32 := FNToFN_module "fpu" 6 6 6 22.
Definition F16ToF64 := FNToFN_module "fpu" 6 6 9 51.
Definition F32ToF64 := FNToFN_module "fpu" 6 22 9 51.
Definition F32ToF16 := FNToFN_module "fpu" 6 22 6 6.
Definition F64ToF32 := FNToFN_module "fpu" 9 51 6 22.
Definition F64ToF16 := FNToFN_module "fpu" 9 51 6 6.
