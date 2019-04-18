Require Import Kami.Syntax Definitions Classify.

Section ModClassify.
  Variable name: string.
  Local Notation "^ x" := (name ++ "#" ++ x)%string (at level 100).

  Variable expWidthMinus2 sigWidthMinus2: nat.
  Variable lenMinus10: nat.
  Definition ClassifyImpl :=
    MODULE {
        (* Register "test": Bool <- false *)
        (* with RegisterU "test2": Bool *)
        (* with *)
        Rule ^"classify" :=
          Call fn : FN expWidthMinus2 sigWidthMinus2 <- "classifyInput" ();
          Call "classifyOutput" (classify_impl #fn lenMinus10 : Bit (10 + lenMinus10));
          Retv
      }.

  Definition ClassifySpec :=
    MODULE {
        Rule ^"classify" :=
          Call fn : FN expWidthMinus2 sigWidthMinus2 <- "classifyInput" ();
          Call "classifyOutput" (classify_spec #fn lenMinus10 : Bit (10 + lenMinus10));
          Retv
      }.
End ModClassify.
