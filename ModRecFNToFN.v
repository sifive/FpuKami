Require Import Definitions String Kami.Syntax.

Section FNFromRecFN.
  Variable name: string.
  Variable expWidthMinus2 sigWidthMinus2: nat.
  Local Notation "^ x" := (name ++ "#" ++ x)%string (at level 100).

  Open Scope kami_expr.
  
  Definition RecFNToFN_module :=
    MODULE {
        Rule ^"RecFNToFN" :=
          Call input: RecFN expWidthMinus2 sigWidthMinus2  <- "input" ();
          LET nf <- getNF_from_RecFN #input;
          Call "nf" (#nf: _);
          LET recfn <- getFN_from_NF #nf;
          (* LET recfn: _ <- (getFN_from_RecFN #input); *)
          Call "output" (#recfn: _);
          Retv
      }.
  Close Scope kami_expr.

End FNFromRecFN.

Definition RecF16ToF16 := RecFNToFN_module "fpu" 6 6.
Definition RecF32ToF32 := RecFNToFN_module "fpu" 6 22.
Definition RecF64ToF64 := RecFNToFN_module "fpu" 9 51.

