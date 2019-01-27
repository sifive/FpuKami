Require Import Definitions MulAdd String Kami.Syntax Round.

Section FpuMulAdd.
  Variable name: string.
  Variable expWidthMinus2 sigWidthMinus2: nat.
  Variable out_expWidthMinus2 out_sigWidthMinus2: nat.
  Local Notation "^ x" := (name ++ "#" ++ x)%string (at level 100).

  Open Scope kami_expr.
  Definition MulAddMod :=
    MODULE {
        Rule ^"MulAdd" :=
          Call inputA: FN expWidthMinus2 sigWidthMinus2  <- "inputA" ();
          Call inputB: FN expWidthMinus2 sigWidthMinus2  <- "inputB" ();
          Call inputC: FN expWidthMinus2 sigWidthMinus2  <- "inputC" ();
          Call tiny: Bool <- "tiny" ();
          Call roundMode: Bit 3 <- "roundMode" ();
          Call op: Bit 2 <- "op" ();
          LET inputANF <- getNF_from_FN #inputA;
          LET inputBNF <- getNF_from_FN #inputB;
          LET inputCNF <- getNF_from_FN #inputC;
          LET mulAddInput: MulAdd_Input expWidthMinus2 sigWidthMinus2
                                        <- STRUCT {
                                          "op" ::= #op;
                                          "a" ::= (#inputANF);
                                          "b" ::= (#inputBNF);
                                          "c" ::= (#inputCNF);
                                          "roundingMode" ::= (#roundMode);
                                          "detectTininess" ::= (#tiny)
                                        };
          LETA MulAdd : OpOutput expWidthMinus2 sigWidthMinus2 <-
                                MulAdd_action #mulAddInput;
          
          LET muladdOutput <- ((#MulAdd) @% "out") ;
          Call "exceptionFlags" (#MulAdd @% "exceptionFlags": _) ;
          Call "inputANF" (#inputANF: _) ;
          Call "inputBNF" (#inputBNF: _) ;
          Call "inputCNF" (#inputCNF: _) ;
          Call "inputAFN" (#inputA: _) ;
          Call "inputBFN" (#inputB: _) ;
          Call "inputCFN" (#inputC: _) ;
          Call "outputNF" (#muladdOutput: _) ;
          Call "outputFN" ((getFN_from_NF #muladdOutput): _);
          Call "stuff" ((nonSpecializedFrac #muladdOutput): _);
          Call "isSubnormalExp" (isSubnormalExp #muladdOutput: _ );
        Retv
      }.
  Close Scope kami_expr.

End FpuMulAdd.

Definition MulAddF16 := MulAddMod "fpu" 3 9.
Definition MulAddF32 := MulAddMod "fpu" 6 22.
Definition MulAddF64 := MulAddMod "fpu" 9 51.