Require Import Definitions INToNF String Kami.All Round.

Section INToFN.
  Variable name: string.
  Variable szMinus2: nat.
  Variable out_expWidthMinus2 out_sigWidthMinus2: nat.
  Local Notation "^ x" := (name ++ "#" ++ x)%string (at level 100).
  Local Notation sz := (szMinus2 + 1 + 1).

  Open Scope kami_expr.
  Definition INToFNMod :=
    MODULE {
        Rule ^"INToFN" :=
          Call input: Bit sz  <- "inputIN" ();
          Call signedIn: Bool <- "signedIn" ();
          Call roundMode: Bit 3 <- "roundMode" ();
          Call tiny: Bool <- "tiny" ();

          LET InToNFInput: INToNFInput szMinus2 <- STRUCT {
                                          "in" ::= #input;
                                          "signedIn" ::= #signedIn;
                                          "afterRounding" ::= #tiny;
                                          "roundingMode" ::= #roundMode
                                        };
          LETA INToNF : OpOutput out_expWidthMinus2 out_sigWidthMinus2 <-
                                INToNF_action out_expWidthMinus2 out_sigWidthMinus2 #InToNFInput;
          
          Call "exceptionFlags" (#INToNF @% "exceptionFlags": _) ;
          Call "outputFN" ((getFN_from_NF (#INToNF @% "out")): _);
        Retv
      }.
  Close Scope kami_expr.

End INToFN.

Definition I32ToF32 := INToFNMod "fpu" 30 6 22.
Definition I32ToF64 := INToFNMod "fpu" 30 9 51.
Definition I64ToF32 := INToFNMod "fpu" 62 6 22.
Definition I64ToF64 := INToFNMod "fpu" 62 9 51.
Definition I32ToF16 := INToFNMod "fpu" 30 6 6.
Definition I64ToF16 := INToFNMod "fpu" 62 6 6.
