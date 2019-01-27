Require Import Definitions String Kami.Syntax.

Section FpuRecFNFromFN.
  Variable name: string.
  Variable expWidthMinus2 sigWidthMinus2: nat.
  Local Notation "^ x" := (name ++ "#" ++ x)%string (at level 100).

  Open Scope kami_expr.
  Definition FNToRecFN_module :=
    MODULE {
        Rule ^"FNToRecFN" :=
          Call input: FN expWidthMinus2 sigWidthMinus2  <- "input" ();
          Call "output" ((getRecFN_from_FN #input): _);
        Retv
      }.
 
End FpuRecFNFromFN.


Definition F16ToRecF16 := FNToRecFN_module "fpu" 6 6.
Definition F32ToRecF32 := FNToRecFN_module "fpu" 6 22.
Definition F64ToRecF64 := FNToRecFN_module "fpu" 9 51.

