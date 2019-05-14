Require Import Vector.
Import VectorNotations.
Require Import Kami.All Definitions Classify Round FpuProperties.
Require Import List.
Import ListNotations.

(*
  The following section was inlined from Multicycle.v in ModulesKami.
*)
Section Combinational.
  Variable inpK outK opK k: Kind.
  Variable numIter: nat.
  Notation numIterSz := (Nat.log2_up (numIter + 2)).
  Variable loopFn: forall ty, opK @# ty -> Bit numIterSz @# ty -> LetExprSyntax ty k -> LetExprSyntax ty k.
  Variable evalLoopFn: type opK -> word numIterSz -> type k -> type k.
  Variable evalLoopFn_prop: forall op n e,
      evalLetExpr (loopFn op n e) = evalLoopFn (evalExpr op) (evalExpr n) (evalLetExpr e).
  Variable isLoop: forall ty, inpK @# ty -> Bool @# ty.
  Variable getLoopInit: forall ty, inpK @# ty -> k @# ty.
  Variable getNonLoopVal: forall ty, inpK @# ty -> k @# ty.
  Variable getOutput: forall ty, opK @# ty -> k @# ty -> LetExprSyntax ty outK.
  Variable getOp: forall ty, inpK @# ty -> opK @# ty.
  Variable combine1 combine2 combine3 combine4:
    forall ty, opK @# ty -> Bit numIterSz @# ty -> k @# ty -> Bool @# ty.
  
  Fixpoint comb_loop ty op n (e: LetExprSyntax ty k) :=
    match n with
    | 0 => e
    | S m => comb_loop op m (loopFn op ($m)%kami_expr e)
    end.
End Combinational.

Section DivSqrt.
  Variable expWidthMinus2 sigWidthMinus2: nat.
  
  Local Notation expWidthMinus1 := (expWidthMinus2 + 1).
  Local Notation expWidth := (expWidthMinus1 + 1).

  Local Notation sigWidthMinus1 := (sigWidthMinus2 + 1).
  Local Notation sigWidth := (sigWidthMinus1 + 1).

  Local Notation sigWidthPlus1 := (sigWidth + 1).
  Local Notation sigWidthPlus2 := (sigWidthPlus1 + 1).

  Definition inpK := STRUCT_TYPE {
                         "isSqrt" :: Bool ;
                         "nfA"    :: NF expWidthMinus2 sigWidthMinus2 ;
                         "nfB"    :: NF expWidthMinus2 sigWidthMinus2 ;
                         "round"  :: Bit 3 ;
                         "tiny"   :: Bool }.

  Definition outK := STRUCT_TYPE {
                         "isSqrt"      :: Bool ;
                         "inNf"        :: NF expWidthMinus2 sigWidthPlus1 ;
                         "outNf"       :: NF expWidthMinus2 sigWidthMinus2 ;
                         "outNFException" :: ExceptionFlags ;
                         (* "out"         :: RecFN expWidthMinus2 sigWidthMinus2 ; *)
                         (* "outFN"       :: FN expWidthMinus2 sigWidthMinus2 ; *)
                         "exception"   :: ExceptionFlags;
                         "invalidExc"  :: Bool ;
                         "infiniteExc" :: Bool }.

  Definition opK := STRUCT_TYPE {
                        "isLess"      :: Bool ;
                        "isSqrt"      :: Bool ;
                        "round"       :: Bit 3 ;
                        "tiny"        :: Bool ;
                        "sigB"        :: Bit sigWidthMinus1 ;
                        "isNaN"       :: Bool ;
                        "isInf"       :: Bool ;
                        "isZero"      :: Bool ;
                        "sign"        :: Bool ;
                        "sExp"        :: Bit (expWidth + 1) ;
                        "majorExc"    :: Bool ;
                        "oddExp"      :: Bool}.

  Definition k := STRUCT_TYPE {
                      "sig"         :: Bit (sigWidthPlus2) ;
                      "rem"         :: Bit (sigWidthPlus2) ;
                      "summary"     :: Bool }.

  Definition numIter := sigWidthPlus2.

  Axiom cheat: forall t, t.

  Local Open Scope kami_expr.
  Definition isLoop ty (inp: inpK @# ty): Bool @# ty :=
    let rawA := (inp @% "nfA") in
    let rawB := (inp @% "nfB") in
    let specialCaseA := rawA @% "isNaN" || rawA @% "isInf" || rawA @% "isZero" in
    let specialCaseB := rawB @% "isNaN" || rawB @% "isInf" || rawB @% "isZero" in
    let normalCase_div := (! specialCaseA) && (! specialCaseB) in
    let normalCase_sqrt := (! specialCaseA) && (! (rawA @% "sign")) in
    IF inp @% "isSqrt" then normalCase_sqrt else normalCase_div.

  Definition getOp ty (inp: inpK @# ty) : opK @# ty.
    refine (
        let rawA := (inp @% "nfA") in
        let rawB := (inp @% "nfB") in
        let isInf := (IF inp @% "isSqrt"
                      then rawA @% "isInf"
                      else rawA @% "isInf" || rawB @% "isZero") in
        let isZero := (IF inp @% "isSqrt"
                       then rawA @% "isZero"
                       else rawA @% "isZero" || rawB @% "isInf") in
        let sign := (IF inp @% "isSqrt"
                     then rawA @% "sign"
                     else (rawA @% "sign") ^^ (rawB @% "sign")) in
        let NaN_div := ((rawA @% "isZero") && (rawB @% "isZero")) || ((rawA @% "isInf") && (rawB @% "isInf")) in
        let NaN_sqrt := ((! (rawA @% "isNaN")) && (! (rawA @% "isZero"))) && (rawA @% "sign") in
        let majorExc := (IF inp @% "isSqrt"
                         then ((isSigNaNRawFloat rawA) || NaN_sqrt)
                         else ((((isSigNaNRawFloat rawA) || (isSigNaNRawFloat rawB)) || NaN_div) ||
                               (((! (rawA @% "isNaN")) && (! (rawA @% "isInf"))) && (rawB @% "isZero")))) in
        let lsbExp := UniBit (TruncLsb 1 expWidth) (castBits _ (rawA @% "sExp")) in
        let isLess := rawA @% "sig" < rawB @% "sig" in
        let newExp := (IF rawB @% "sign"
                       then (rawA @% "sExp") + (rawB @% "sExp")
                       else (rawA @% "sExp") - (rawB @% "sExp")) in
        (STRUCT { "isLess"      ::= isLess ;
                  "isSqrt"      ::= inp @% "isSqrt" ;
                  "round"       ::= inp @% "round" ;
                  "tiny"        ::= inp @% "tiny" ;
                  "sigB"        ::= rawB @% "sig" ;
                  "isNaN"       ::= (IF inp @% "isSqrt"
                                     then rawA @% "isNaN" || NaN_sqrt
                                     else rawA @% "isNaN" || rawB @% "isNaN" || NaN_div) ;
                  "isInf"       ::= isInf ;
                  "isZero"      ::= isZero ;
                  "sign"        ::= sign ;
                  "sExp"        ::= (IF inp @% "isSqrt"
                                     then (rawA @% "sExp") >>> $$ WO~1
                                     else (IF isLess
                                           then newExp - $1
                                           else newExp));
                  "majorExc"    ::= majorExc ;
                  "oddExp"      ::= lsbExp == $1
      })); clear; abstract (Omega.omega).
  Defined.

  Definition getLoopInit ty (inp: inpK @# ty) : k @# ty.
    refine
      (let rawA := (inp @% "nfA") in
       let a_width_sigWidthPlus1 := {< $$ WO~0, $$ WO~0, $$ WO~1, rawA @% "sig" >} << $$ WO~1 in
       let a_width_sigWidth := {< $$ WO~0, $$ WO~0, $$ WO~1, rawA @% "sig" >} in
       let a_width_sigWidthPlus2 := a_width_sigWidthPlus1 << $$ WO~1 in
       let a2_width_sigWidthPlus1 := a_width_sigWidthPlus1 << $$ WO~1 in
       let a2_width_sigWidthPlus2 := a2_width_sigWidthPlus1 << $$ WO~1 in
       let lsbExp := UniBit (TruncLsb 1 expWidth) (castBits _ (rawA @% "sExp")) in
       (* let rem := (IF (inp @% "isSqrt") *)
       (*             then (IF lsbExp == $1 *)
       (*                   then a2_width_sigWidthPlus1 *)
       (*                   else a_width_sigWidthPlus1) >> $$ WO~1 *)
       (*             else a_width_sigWidth) in *)
       let rem := (IF (inp @% "isSqrt")
                   then (IF lsbExp == $1
                         then a_width_sigWidthPlus1
                         else a_width_sigWidth)
                   else a_width_sigWidth) in
       (STRUCT {"sig"     ::= $ 0 ;
                "rem"     ::= rem ;
                "summary" ::= rem != $ 0}) : k @# ty).
    abstract (clear; Omega.omega).
  Defined.

  Definition getNonLoopVal := getLoopInit.

  Local Notation mul c v := (IF c then v else $0)%kami_expr.
  Definition loopFn ty (op: opK @# ty) (iter: Bit (Nat.log2_up (numIter + 2)) @# ty)
             (accumIn: LetExprSyntax ty k): LetExprSyntax ty k.
    refine
      (LETE bit : Bit (sigWidthPlus2 + 1) <- RetE ($1 << iter);
       LETE accum : k <- accumIn;
       LETE sig2 : Bit (sigWidthPlus2 + 1) <- RetE (({< $$ WO~0, #accum @% "sig" >}) << $$ WO~1);
       LETE rem2 : Bit (sigWidthPlus2 + 1) <- RetE (({< $$ WO~0, #accum @% "rem" >}) << $$ WO~1);
       LETE b_width_sigWidth : Bit (sigWidthPlus2 + 1) <- RetE ({< $$ WO~0, $$ WO~0, $$ WO~0, $$ WO~1, op @% "sigB" >});
       LETE b2_width_sigWidth: Bit (sigWidthPlus2 + 1) <- RetE (#b_width_sigWidth << $$ WO~1);
       LETE trialTerm : Bit (sigWidthPlus2 + 1) <- RetE (IF op @% "isSqrt"
                                                         then #sig2 | #bit
                                                         else #b2_width_sigWidth);
       LETE c : Bool <- RetE (#rem2 >= #trialTerm);
       LETE newSig : Bit sigWidthPlus2 <- RetE (#accum @% "sig" | UniBit (TruncLsb _ 1) (mul #c #bit));
       LETE newRem : Bit (sigWidthPlus2 + 1)<- RetE (#rem2 - mul #c #trialTerm);
       LETE newSummary : Bool <- RetE (#newRem != $0);
       LETE newAccum: k <- RetE (STRUCT {"sig"     ::= #newSig ;
                                         "rem"     ::= (* UniBit (TruncLsb _ 1) #newRem *)
                                           (IF iter != $0
                                            then UniBit (TruncLsb _ 1) #newRem
                                            else #accum @% "rem");
                                         "summary" ::= (* #numSummary *)
                                           IF #c then #newSummary else #accum @% "summary"});
       LETE msbSig <- RetE (UniBit (TruncMsb _ 1) (#accum @% "sig"));
       RetE (IF (op @% "isSqrt" && iter == ($sigWidth + $1))
             || (iter == $0 && #msbSig == $1)
             then #accum
             else #newAccum)).
  Defined.

  Definition getOutput ty (op: opK @# ty) (accum: k @# ty): LetExprSyntax ty outK.
    refine (
        LETE fullSig : Bit (1 + sigWidthPlus1) <- RetE ({< UniBit (TruncLsb _ 1) (accum @% "sig"),
                                                         pack (accum @% "summary") >});
        LETE invalidExc : Bool <- RetE ((op @% "majorExc") && (op @% "isNaN"));
        LETE infiniteExc : Bool <- RetE ((op @% "majorExc") && ! (op @% "isNaN"));
        LETE nf1 : NF expWidthMinus2 sigWidthPlus1 <-
                      RetE (STRUCT { "isNaN" ::= ((op @% "isNaN"));
                                     "isInf" ::= ((op @% "isInf"));
                                     "isZero" ::= op @% "isZero" ;
                                     "sign" ::= op @% "sign" ;
                                     "sExp" ::= op @% "sExp" ;
                                     "sig" ::= castBits _ (IF op @% "isLess" || (op @% "isSqrt")
                                                           then (#fullSig << $$ WO~1)
                                                           else #fullSig) });
        LETE nf: NF expWidthMinus2 sigWidthPlus1 <-
                    RetE (STRUCT { "isNaN" ::= ((#nf1 @% "isNaN") || #invalidExc);
                                   "isInf" ::= ((#nf1 @% "isInf") || #infiniteExc);
                                   "isZero" ::= #nf1 @% "isZero" ;
                                   "sign" ::= #nf1 @% "sign" ;
                                   "sExp" ::= #nf1 @% "sExp" ;
                                   "sig" ::= #nf1 @% "sig" });
        LETE roundIn : RoundInput expWidthMinus2 _ <- RetE (STRUCT { "in" ::= #nf ;
                                                                     "afterRounding" ::= op @% "tiny" ;
                                                                     "roundingMode" ::= op @% "round" });
        LETE roundedNF: OpOutput expWidthMinus2 sigWidthMinus2 <- RoundNF_def_expr _ _ #roundIn;
        LETE roundedNF_out: NF expWidthMinus2 sigWidthMinus2 <- RetE (#roundedNF @% "out");
        LETE roundedNF_except: ExceptionFlags <- RetE (#roundedNF @% "exceptionFlags");
        LETE roundedNF_exception : ExceptionFlags
                                     <-
                                     RetE (STRUCT {
                                               "invalid" ::= #invalidExc;
                                               "infinite" ::= #infiniteExc;
                                               "overflow" ::= #roundedNF_except @% "overflow";
                                               "underflow" ::= #roundedNF_except @% "underflow";
                                               "inexact" ::= #roundedNF_except @% "inexact" });
        (* LETE rec: RecFN expWidthMinus2 sigWidthMinus2 <- RetE (getRecFN_from_NF #roundedNF_out); *)
        (* LETE fn: FN expWidthMinus2 sigWidthMinus2 <- RetE (getFN_from_RecFN #rec); *)
        LETE out: outK <- RetE (STRUCT {
                                    "isSqrt"      ::= op @% "isSqrt";
                                    "inNf"        ::= #nf1;
                                    "outNf"       ::= #roundedNF_out;
                                    "outNFException" ::= #roundedNF_except;
                                    (* "out"         ::= #rec; *)
                                    (* "outFN"       ::= #fn; *)
                                    "exception"   ::= #roundedNF_exception;
                                    "invalidExc"  ::= #invalidExc;
                                    "infiniteExc" ::= #infiniteExc });
        SystemE [
          DispString ty "[ModDivSqrt] op: ";
          DispBinary op;  
          DispString ty "\n"
        ];
        SystemE [
          DispString ty "[ModDivSqrt] accum: ";
          DispBinary accum;  
          DispString ty "\n"
        ];
        SystemE [
          DispString ty "[ModDivSqrt] outK: ";
          DispBinary #out;  
          DispString ty "\n"
        ];
        RetE #out);
      try abstract (simpl; Omega.omega).
  Defined.

  Definition combine1 ty (op: opK @# ty) (n: Bit (Nat.log2_up (numIter + 2)) @# ty)
             (accum: k @# ty) :=
    (n == ($numIter-$1)).

  Definition combine2 ty (op: opK @# ty) (n: Bit (Nat.log2_up (numIter + 2)) @# ty)
             (accum: k @# ty) :=
    ((op @% "isSqrt") && n == ($numIter-$2)).

  Definition combine3 ty (op: opK @# ty) (n: Bit (Nat.log2_up (numIter + 2)) @# ty)
             (accum: k @# ty) :=
    ((op @% "isSqrt") && n == ($numIter-$3) && op @% "oddExp").

  Definition combine4 ty (op: opK @# ty) (n: Bit (Nat.log2_up (numIter + 2)) @# ty)
             (accum: k @# ty) :=
    (n == $0 && (UniBit (TruncMsb sigWidthPlus1 1) (accum @% "sig")) == $1).
  
  Definition div_sqrt_expr ty (input : inpK @# ty)
    :  outK ## ty
    := LETC op : opK <- getOp input;
       LETC initVal
         :  k
         <- getLoopInit input;
       LETE loop_out
         :  k
         <- comb_loop numIter loopFn (#op) numIter (RetE (#initVal));
       getOutput (#op)
         (ITE (isLoop input) (#loop_out) (#initVal)).

  Local Close Scope kami_expr.
(*
  Definition newSeq := seq_module numIter loopFn isLoop getLoopInit getNonLoopVal getOutput getOp combine1 combine2 combine3 combine4 "multi".

  Definition newComb := comb_module numIter loopFn isLoop getLoopInit getNonLoopVal getOutput getOp "multi".

  Definition rtlModParam := makeRtl newSeq nil.
*)
End DivSqrt.
(*
Definition DivSqrt32 := rtlModParam 6 22.
Definition DivSqrt64 := rtlModParam 9 51.
*)
