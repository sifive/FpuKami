Require Import Kami.AllNotations FpuKami.Definitions FpuKami.Round.

  
Section Definitions.
  Open Scope nat.
  Variable szMinus2 outExpWidthMinus2 outSigWidthMinus2: nat.

  Local Notation outExpWidthMinus1 := (outExpWidthMinus2 + 1).
  Local Notation outSigWidthMinus1 := (outSigWidthMinus2 + 1).
  
  Local Notation szMinus1 := (szMinus2 + 1).
  Local Notation sz := (szMinus1 + 1).
  
  Section Ty.
    Variable ty: Kind -> Type.
    Section Convert.

      Definition INToNFInput := STRUCT_TYPE {
                                "in" :: Bit sz;
                                "signedIn" :: Bool;
                                "afterRounding" :: Bool;
                                "roundingMode" :: Bit 3
                              }.

      Open Scope kami_expr.
      Variable input: INToNFInput @# ty.

      Definition signedIn := input @% "signedIn" .
      Definition inputIN  := input @% "in".

      Definition expWidthMinus2 := Nat.log2_up sz.
      Local Notation expWidthMinus1 := (expWidthMinus2 + 1)%nat.
      Local Notation expWidth := (expWidthMinus1 + 1)%nat.


      Open Scope kami_action.

      Definition INToNF_expr
        :  OpOutput outExpWidthMinus2 outSigWidthMinus2 ## ty
        := LETC sign <- signedIn && ((UniBit (TruncMsb szMinus1 1) inputIN) == $1);
           LETC absIn <- IF #sign then $0 - inputIN else inputIN;

           LETC leadingZeros <- countLeadingZeros (sz+1) #absIn;
           
           LETC adjSig <- UniBit (TruncLsb szMinus1 1) (#absIn << #leadingZeros);
           LETC exp <- $sz - #leadingZeros - $1;


           LETC preRoundOutput: NF szMinus2 szMinus2 <-
                                  STRUCT {
                                    "isNaN"  ::= $$false;
                                    "isInf"  ::= $$false;
                                    "isZero" ::= #absIn == $0;
                                    "sign"   ::= #sign;
                                    "sExp"   ::= #exp;
                                    "sig"   ::= #adjSig
                                  };

           LETC roundInput: RoundInput szMinus2 szMinus2 <-
                                      STRUCT {
                                        "in" ::= #preRoundOutput;
                                        "afterRounding" ::= input @% "afterRounding";
                                        "roundingMode" ::= input @% "roundingMode"
                                      };
                                        
           LETE roundOutput <- (RoundNF_expr outExpWidthMinus2 outSigWidthMinus2
                                               (pow2 outExpWidthMinus1 - 2)%nat
                                               (pow2 outExpWidthMinus1 + outSigWidthMinus1 - 2)%nat
                                               (pow2 outExpWidthMinus1 - 1)%nat
                                               #roundInput);
   
           RetE #roundOutput.

      Definition INToNF_action: ActionT ty (OpOutput outExpWidthMinus2 outSigWidthMinus2)
        := convertLetExprSyntax_ActionT INToNF_expr.

    End Convert.

  End Ty.
End Definitions.
