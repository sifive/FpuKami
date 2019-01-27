Require Import Definitions String Kami.Syntax FpuKami.Compare.

Section Compare.
  Variable name: string.
  Variable expWidthMinus2 sigWidthMinus2: nat.
  Local Notation "^ x" := (name ++ "#" ++ x)%string (at level 100).

  Open Scope kami_expr.
  Definition CompareModFN :=
    MODULE {
        Rule ^"CompareFN" :=
        Call inputA: FN expWidthMinus2 sigWidthMinus2  <- "inputA" ();
        Call inputB: FN expWidthMinus2 sigWidthMinus2  <- "inputB" ();

        LET inputANF: NF expWidthMinus2 sigWidthMinus2  <- getNF_from_FN #inputA;
        LET inputBNF: NF expWidthMinus2 sigWidthMinus2 <- getNF_from_FN #inputB;

        LETA compareOutput <- Compare_action #inputANF #inputBNF;
        
        Call "exceptionFlags" (#compareOutput @% "exceptionFlags": _) ;
        Call "gt" (((#compareOutput @% "gt")): _);
        Call "lt" (((#compareOutput @% "lt")): _);
        Call "eq" (((#compareOutput @% "eq")): _);
        
        Retv
      }.

  Definition CompareModRecFN :=
    MODULE {
        Rule ^"CompareRecFN" :=
        Call inputA: RecFN expWidthMinus2 sigWidthMinus2  <- "inputA" ();
        Call inputB: RecFN expWidthMinus2 sigWidthMinus2  <- "inputB" ();

        LET inputANF: NF expWidthMinus2 sigWidthMinus2  <- getNF_from_RecFN #inputA;
        LET inputBNF: NF expWidthMinus2 sigWidthMinus2 <- getNF_from_RecFN #inputB;

        LETA compareOutput <- Compare_action #inputANF #inputBNF;
        
        Call "exceptionFlags" (#compareOutput @% "exceptionFlags": _) ;
        Call "gt" (((#compareOutput @% "gt")): _);
        Call "lt" (((#compareOutput @% "lt")): _);
        Call "eq" (((#compareOutput @% "eq")): _);
        
        Retv
      }.

End Compare.

Definition CompareF16 := CompareModFN "fpu" 6 6.
Definition CompareF32 := CompareModFN "fpu" 6 22.
Definition CompareF64 := CompareModFN "fpu" 9 51.

Definition CompareRecF16 := CompareModRecFN "fpu" 6 6.
Definition CompareRecF32 := CompareModRecFN "fpu" 6 22.
Definition CompareRecF64 := CompareModRecFN "fpu" 9 51.
