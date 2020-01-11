(*
  Correctness proof of CTL model checking algorithm
  Isabelle 2014

  Based on:
  Isabelle/HOL
  A Proof Assistant for Higher-Order Logic
  Tobias Nipkow Lawrence C. Paulson Markus Wenzel
  August 15, 2018
  section 6.6
*)
theory ModelChecking imports Main begin

typedecl state
consts M :: "(state * state)set"
typedecl "atom"
consts L :: "state => atom set"

datatype formula = Atom "atom"
                 | Neg formula
                 | And formula formula
                 | EN formula   (* Next: instead of EX *)
                 | EU formula formula
                 | EG formula

definition Paths :: "state => (nat => state)set" where
  "Paths s == {p. s = p 0 & (ALL i. (p i, p(i+1)) : M)}"

definition FPaths :: "state => state list set" where
  "FPaths s ==
  {p. length p > 0 & s = p!0 & (ALL i<length p - 1. (p!i, p!(i+1)) : M)}"

primrec valid :: "state => formula => bool" ("(_ |= _)" [80,80] 80)
  where
  "s |= Atom a = (a : L s)" |
  "s |= Neg f = (~ (s |= f))" |
  "s |= And f g = (s |= f & s |= g)" |
  "s |= EN f = (EX t. (s,t) : M & t |= f)" |
  "s |= EU f g = (EX p : FPaths s.  p!(length p - 1) |= g & (ALL j<length p - 1. p!j |= f))" |
  "s |= EG f = (EX p : Paths s. ALL i. p i |= f)"

(* E[φUψ] = ψ ∨ (φ ∧ EX E[φUψ]) *)
definition eu :: "state set => state set => state set => state set" where
  "eu A B T == B Un {s. s : A & (EX t. (s, t) : M & t : T)}"

(* EGφ = φ ∧ EX EGφ *)
definition eg :: "state set => state set => state set" where
  "eg A T == A Int {s. EX t. (s, t) : M & t : T}"

primrec mc :: "formula => state set" where
  "mc(Atom a) = {s. a : L s}" |
  "mc(Neg f) = -mc f" |
  "mc(And f g) = mc f Int mc g" |
  "mc(EN f) = {s. EX t. (s,t) : M & t : mc f}" |
  "mc(EU f g) = lfp (eu (mc f) (mc g))" |
  "mc(EG f) = gfp (eg (mc f))"

lemma mono_eu: "mono (eu A B)"
apply(simp add: mono_def eu_def)
apply(blast)
done

lemma mono_eg: "mono (eg A)"
apply(simp add: mono_def eg_def)
apply(blast)
done

primrec path :: "state => (state => bool) => (nat => state)" where
  "path s Q 0 = s" |
  "path s Q (Suc n) = (SOME t. (path s Q n,t) : M & Q t)"

lemma infinity_lemma:
  "[| Q s; ALL s. Q s --> (EX t. (s,t) : M & Q t) |] ==>
  EX p : Paths s. ALL i. Q(p i)"
apply(subgoal_tac
  "EX p. s = p 0 & (ALL i::nat. (p i, p(i+1)) : M & Q(p i))")
apply(simp add: Paths_def, blast)
apply(rule_tac x = "path s Q" in exI)
apply(clarsimp)
apply(induct_tac i)
apply(simp)
apply(fast intro: someI2_ex)
apply(simp)
apply(rule someI2_ex)
apply(blast)
apply(rule someI2_ex)
apply(blast)
apply(blast)
done

theorem EU_lemma1:
  "lfp (eu A B) <= {s. EX p : FPaths s. p!(length p - 1) : B & (ALL j<length p - 1. p!j : A)}"
apply(rule lfp_lowerbound)
apply(auto simp add: eu_def FPaths_def)
apply(rule_tac x="[x]" in exI)
apply(clarsimp)
apply(rule_tac x="x#p" in exI)
apply(auto)
apply(case_tac i)
apply(auto)
apply(case_tac j)
apply(auto)
done

lemma lfp_eu [rule_format]:
  "p ~= [] -->
  (ALL i<length p - Suc 0. (p ! i, p ! Suc i) : M) -->
  p ! (length p - Suc 0) : B -->
  (ALL j<length p - Suc 0. p ! j : A) -->
  p ! 0 : lfp (eu A B)"
apply(induct_tac p)
apply(clarsimp)
apply(clarsimp)
apply(case_tac list)
apply(clarsimp)
apply(subst lfp_unfold[OF mono_eu])
apply(subst eu_def)
apply(clarsimp)
apply(clarsimp)
apply(drule mp)
apply(clarsimp)
apply(drule_tac x="i+1" in spec)
apply(rotate_tac -1)
apply(drule mp)
apply(clarsimp)
apply(clarsimp)
apply(drule mp)
apply(clarsimp)
apply(rotate_tac -2)
apply(drule_tac x="j+1" in spec)
apply(rotate_tac -1)
apply(drule mp)
apply(clarsimp)
apply(clarsimp)
apply(subst lfp_unfold[OF mono_eu])
apply(subst eu_def)
apply(clarify)
apply(rule)
apply (metis nth_Cons_0 zero_less_Suc)
apply(rule_tac x="aa" in exI)
apply(clarsimp)
by (metis nth_Cons_0 zero_less_Suc)

theorem EU_lemma2:
  "{s. EX p : FPaths s. p!(length p - 1) : B & (ALL j<length p - 1. p!j : A)} <= lfp (eu A B)"
apply(unfold FPaths_def)
apply(clarsimp)
apply(rule lfp_eu)
apply(auto)
done

lemma gfp_eg [rule_format]: "x : gfp (eg A) --> x : A"
apply(subst gfp_unfold[OF mono_eg])
apply(subst eg_def)
apply(clarsimp)
done

lemma EG_lemma1:
  "gfp (eg A) <= {s. EX p : Paths s. ALL i. p i : A}"
apply(clarsimp)
apply(drule_tac Q="%x. x : gfp (eg A)" in infinity_lemma)
apply(subst gfp_unfold[OF mono_eg])
apply(clarsimp)
apply(simp add: eg_def)
apply(clarsimp)
apply(rule_tac x="p" in bexI)
apply(clarsimp)
apply(drule_tac x="i" in spec)
apply(drule gfp_eg)
apply(assumption)
apply(assumption)
done

lemma EG_lemma2:
  "{s. EX p : Paths s. ALL i. p i : A} <= gfp (eg A)"
apply(rule coinduct)
apply(rule mono_eg)
apply(clarsimp)
apply(simp add: eg_def)
apply(unfold Paths_def)
apply(clarsimp)
apply(rule_tac x="p 1" in exI)
apply(clarsimp)
apply(rule_tac x="%k. p (Suc k)" in exI)
apply(clarsimp)
done

theorem "mc f = {s. s |= f}"
apply(induct_tac f)
apply(auto simp add: equalityI[OF EU_lemma1 EU_lemma2] equalityI[OF EG_lemma1 EG_lemma2])
done

end
