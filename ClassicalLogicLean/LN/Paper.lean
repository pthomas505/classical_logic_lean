import ClassicalLogicLean.LN.Binders
import ClassicalLogicLean.LN.Semantics
import MathlibExtraLean.List
import MathlibExtraLean.Finset


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


namespace LN

open Var Formula


def Var.open
  (j : ℕ)
  (v : Var) :
  Var → Var
  | free_ x => free_ x
  | bound_ i =>
      if i < j
      then bound_ i
      else
        if i = j
        then v
        else bound_ (i - 1)


def Formula.open
  (j : ℕ)
  (v : Var) :
  Formula → Formula
  | pred_ X vs => pred_ X (vs.map (Var.open j v))
  | not_ phi => not_ (Formula.open j v phi)
  | imp_ phi psi => imp_ (Formula.open j v phi) (Formula.open j v psi)
  | forall_ x phi => forall_ x (Formula.open (j + 1) v phi)


def Var.openList
  (j : Nat)
  (us : List Var) : Var → Var
  | free_ x => free_ x
  | bound_ i =>
      if i < j
      then bound_ i
      else
        let i := i - j
        if _ : i < us.length
        then us[i]
        else bound_ (i - us.length + j)


def Formula.openList
  (j : ℕ)
  (us : List Var) :
  Formula → Formula
  | pred_ X vs => pred_ X (vs.map (Var.openList j us))
  | not_ phi => not_ (Formula.openList j us phi)
  | imp_ phi psi => imp_ (Formula.openList j us phi) (Formula.openList j us psi)
  | forall_ x phi => forall_ x (Formula.openList (j + 1) us phi)


def Var.close
  (j : ℕ)
  (v : Var) :
  Var → Var
  | free_ x =>
      if free_ x = v
      then bound_ j
      else free_ x
  | bound_ i =>
      if i < j
      then bound_ i
      else bound_ (i + 1)


def Formula.close
  (j : ℕ)
  (v : Var) :
  Formula → Formula
  | pred_ X vs => pred_ X (vs.map (Var.close j v))
  | not_ phi => not_ (Formula.close j v phi)
  | imp_ phi psi => imp_ (Formula.close j v phi) (Formula.close j v psi)
  | forall_ x phi => forall_ x (Formula.close (1 + j) v phi)


def Var.subst (v t : Var) : Var → Var
  | free_ x =>
      if v = free_ x
      then t
      else free_ x
  | bound_ i => bound_ i


def Formula.subst (v t : Var) : Formula → Formula
  | pred_ X vs => pred_ X (vs.map (Var.subst v t))
  | not_ phi => not_ (Formula.subst v t phi)
  | imp_ phi psi => imp_ (Formula.subst v t phi) (Formula.subst v t psi)
  | forall_ x phi => forall_ x (Formula.subst v t phi)


def Var.substFun (σ : Var → Var) : Var → Var
  | free_ x => σ (free_ x)
  | bound_ i => bound_ i


def Formula.substFun (σ : Var → Var) : Formula → Formula
  | pred_ X vs => pred_ X (vs.map (Var.substFun σ))
  | not_ phi => not_ (phi.substFun σ)
  | imp_ phi psi => imp_ (phi.substFun σ) (psi.substFun σ)
  | forall_ x phi => forall_ x (phi.substFun σ)


def Formula.predSub
  (τ : String → ℕ → Formula) :
  Formula → Formula
  | pred_ X vs => Formula.openList 0 vs (τ X vs.length)
  | not_ phi => not_ (phi.predSub τ)
  | imp_ phi psi => imp_ (phi.predSub τ) (psi.predSub τ)
  | forall_ x phi => forall_ x (phi.predSub τ)


inductive Formula.lc : Formula → Prop
  | pred_
    (X : String)
    (vs : List Var) :
    (∀ (v : Var), v ∈ vs → v.isFree) →
    lc (pred_ X vs)

  | not_
    (phi : Formula) :
    lc phi →
    lc (not_ phi)

  | imp_
    (phi psi : Formula) :
    lc phi →
    lc psi →
    lc (imp_ phi psi)
/-
  | forall_
    (x : String)
    (phi : Formula) :
    (∀ (z : String), lc (Formula.open 0 (Var.free_ z) phi)) →
    lc (forall_ x phi)
-/
  | forall_
    (x : String)
    (phi : Formula)
    (z : String) :
    lc (Formula.openList 0 [Var.free_ z] phi) →
    lc (forall_ x phi)


def Var.lc_at
  (j : ℕ) :
  Var → Prop
  | free_ _ => True
  | bound_ i => i < j


def Formula.lc_at
  (j : ℕ) :
  Formula → Prop
  | pred_ _ vs => ∀ (v : Var), v ∈ vs → Var.lc_at j v
  | not_ phi => Formula.lc_at j phi
  | imp_ phi psi => (Formula.lc_at j phi) ∧ (Formula.lc_at j psi)
  | forall_ _ phi => Formula.lc_at (j + 1) phi


--------------------------------------------------


lemma lc_at_zero_iff_is_free
  (v : Var) :
  Var.lc_at 0 v ↔ v.isFree :=
  by
  cases v
  case free_ x =>
    simp only [Var.lc_at]
    simp only [isFree]
  case bound_ i =>
    simp only [Var.lc_at]
    simp only [isFree]
    simp only [not_lt_zero]


--------------------------------------------------


lemma free_var_list_to_string_list
  (vs : List Var)
  (h1 : ∀ (v : Var), v ∈ vs → Var.lc_at 0 v) :
  ∃ (xs : List String), vs = List.map free_ xs :=
  by
  induction vs
  case nil =>
    apply Exists.intro []
    simp only [List.map_nil]
  case cons hd tl ih =>
    simp only [List.mem_cons] at h1
    simp only [forall_eq_or_imp] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    specialize ih h1_right
    obtain ⟨xs, ih⟩ := ih

    cases hd
    case free_ x =>
      apply Exists.intro (x :: xs)
      rewrite [ih]
      simp only [List.map_cons]
    case bound_ i =>
      simp only [Var.lc_at] at h1_left
      simp only [not_lt_zero] at h1_left


--------------------------------------------------

-- 1.

lemma VarOpenFreeVarSet
  (j : ℕ)
  (z : String)
  (v : Var) :
  (Var.open j (free_ z) v).freeVarSet ⊆ v.freeVarSet ∪ {free_ z} :=
  by
  cases v
  case free_ x =>
    simp only [Var.open]
    simp only [Var.freeVarSet]
    simp only [Finset.singleton_union, Finset.singleton_subset_iff]
    apply Finset.mem_insert_self
  case bound_ i =>
    simp only [Var.open]
    split
    case isTrue c1 =>
      simp only [Var.freeVarSet]
      simp only [Finset.empty_union]
      apply Finset.empty_subset
    case isFalse c1 =>
      split
      case isTrue c2 =>
        simp only [Var.freeVarSet]
        simp only [Finset.empty_union, subset_refl]
      case isFalse c2 =>
        simp only [Var.freeVarSet]
        simp only [Finset.empty_union]
        apply Finset.empty_subset


lemma FormulaOpenFreeVarSet
  (j : ℕ)
  (z : String)
  (F : Formula) :
  (Formula.open j (free_ z) F).freeVarSet ⊆ F.freeVarSet ∪ {free_ z} :=
  by
  induction F generalizing j
  case pred_ X vs =>
    simp only [Formula.open]
    simp only [Formula.freeVarSet]
    simp only [Finset.biUnion_subset_iff_forall_subset, List.mem_toFinset, List.mem_map, forall_exists_index]
    intro u v a1
    obtain ⟨a1_left, a1_right⟩ := a1

    trans Var.freeVarSet v ∪ {free_ z}
    · rewrite [← a1_right]
      apply VarOpenFreeVarSet
    · apply Finset.union_subset_union_left
      apply Finset.subset_biUnion_of_mem
      simp only [List.mem_toFinset]
      exact a1_left
  case not_ phi phi_ih =>
    simp only [Formula.open]
    simp only [Formula.freeVarSet]
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.open]
    simp only [Formula.freeVarSet]
    apply Finset.union_subset_union_left_right
    · apply phi_ih
    · apply psi_ih
  case forall_ x phi phi_ih =>
    simp only [Formula.open]
    simp only [Formula.freeVarSet]
    apply phi_ih


--------------------------------------------------


-- 1. for list

lemma VarOpenListFreeVarSet
  (j : ℕ)
  (zs : List String)
  (v : Var) :
  (Var.openList j (zs.map free_) v).freeVarSet ⊆ v.freeVarSet ∪ (zs.map free_).toFinset :=
  by
  cases v
  case free_ x =>
    simp only [Var.openList]
    simp only [Var.freeVarSet]
    simp only [Finset.singleton_union, Finset.singleton_subset_iff]
    apply Finset.mem_insert_self
  case bound_ i =>
    simp only [Var.openList]
    split
    case isTrue c1 =>
      simp only [Var.freeVarSet]
      simp only [Finset.empty_union, Finset.empty_subset]
    case isFalse c2 =>
      split
      case isTrue c3 =>
        simp only [List.length_map] at c3

        simp only [List.getElem_map]
        simp only [Var.freeVarSet]
        simp only [Finset.empty_union]
        simp only [Finset.singleton_subset_iff, List.mem_toFinset, List.mem_map]

        apply Exists.intro (zs[i - j])
        constructor
        · apply List.getElem_mem
        · apply Eq.refl
      case isFalse c3 =>
        simp only [Var.freeVarSet]
        apply Finset.empty_subset


lemma FormulaOpenListFreeVarSet
  (j : ℕ)
  (zs : List String)
  (F : Formula) :
  (Formula.openList j (zs.map free_) F).freeVarSet ⊆ F.freeVarSet ∪ (zs.map free_).toFinset :=
  by
  induction F generalizing j
  case pred_ X vs =>
    simp only [Formula.openList]
    simp only [Formula.freeVarSet]
    simp only [Finset.biUnion_subset_iff_forall_subset, List.mem_toFinset, List.mem_map,
      forall_exists_index]
    intro u v a1
    obtain ⟨a1_left, a1_right⟩ := a1

    trans v.freeVarSet ∪ (zs.map free_).toFinset
    · rewrite [← a1_right]
      apply VarOpenListFreeVarSet
    · apply Finset.union_subset_union_left
      apply Finset.subset_biUnion_of_mem
      simp only [List.mem_toFinset]
      exact a1_left
  case not_ phi phi_ih =>
    simp only [Formula.openList]
    simp only [Formula.freeVarSet]
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.openList]
    simp only [Formula.freeVarSet]
    apply Finset.union_subset_union_left_right
    · apply phi_ih
    · apply psi_ih j
  case forall_ x phi phi_ih =>
    simp only [Formula.openList]
    simp only [Formula.freeVarSet]
    apply phi_ih


--------------------------------------------------


-- 2.

lemma VarOpenFreeVarSet'
  (j : ℕ)
  (z : String)
  (v : Var) :
  v.freeVarSet ⊆ (Var.open j (free_ z) v).freeVarSet :=
  by
  cases v
  case free_ x =>
    simp only [Var.open]
    simp only [Var.freeVarSet]
    apply Set.Subset.refl
  case bound_ i =>
    simp only [Var.open]
    split
    case isTrue c1 =>
      simp only [Var.freeVarSet]
      apply Set.Subset.refl
    case isFalse c1 =>
      split
      case isTrue c2 =>
        simp only [Var.freeVarSet]
        apply Finset.empty_subset
      case isFalse c2 =>
        simp only [Var.freeVarSet]
        apply Set.Subset.refl


lemma FormulaOpenFreeVarSet'
  (j : ℕ)
  (z : String)
  (F : Formula) :
  F.freeVarSet ⊆ (Formula.open j (free_ z) F).freeVarSet :=
  by
  induction F generalizing j
  case pred_ X vs =>
    simp only [Formula.open]
    simp only [Formula.freeVarSet]
    simp only [Finset.biUnion_subset_iff_forall_subset, List.mem_toFinset]
    intro v a1

    trans Var.freeVarSet (Var.open j (free_ z) v)
    · apply VarOpenFreeVarSet'
    · apply Finset.subset_biUnion_of_mem
      simp only [List.mem_toFinset, List.mem_map]
      apply Exists.intro v
      exact ⟨a1, rfl⟩
  case not_ phi phi_ih =>
    simp only [Formula.open]
    simp only [Formula.freeVarSet]
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.open]
    simp only [Formula.freeVarSet]
    apply Finset.union_subset_left_right
    · apply phi_ih
    · apply psi_ih j
  case forall_ x phi phi_ih =>
    simp only [Formula.open]
    simp only [Formula.freeVarSet]
    apply phi_ih


--------------------------------------------------

-- 3.

lemma VarCloseFreeVarSet
  (j : ℕ)
  (z : String)
  (v : Var) :
  (Var.close j (free_ z) v).freeVarSet ⊆ v.freeVarSet \ {free_ z} :=
  by
  cases v
  case free_ x =>
    simp only [Var.close]
    split
    case isTrue c1 =>
      simp only [Var.freeVarSet]
      simp only [Finset.empty_subset]
    case isFalse c1 =>
      simp only [Var.freeVarSet]
      simp only [Finset.singleton_subset_iff, Finset.mem_sdiff]
      constructor
      · simp only [Finset.mem_singleton]
      · simp only [Finset.mem_singleton]
        exact c1
  case bound_ i =>
    simp only [Var.close]
    split
    case isTrue c1 =>
      simp only [Var.freeVarSet]
      simp only [Finset.empty_sdiff]
      apply Set.Subset.refl
    case isFalse c1 =>
      simp only [Var.freeVarSet]
      simp only [Finset.empty_sdiff]
      apply Set.Subset.refl


lemma FormulaCloseFreeVarSet
  (j : ℕ)
  (z : String)
  (F : Formula) :
  (Formula.close j (free_ z) F).freeVarSet ⊆ F.freeVarSet \ {free_ z} :=
  by
  induction F generalizing j
  case pred_ X vs =>
    simp only [Formula.close]
    simp only [Formula.freeVarSet]
    simp only [Finset.biUnion_subset_iff_forall_subset, List.mem_toFinset, List.mem_map,
      forall_exists_index]
    intro u v a1
    obtain ⟨a1_left, a1_right⟩ := a1
    rewrite [← a1_right]

    trans Var.freeVarSet v \ {free_ z}
    · apply VarCloseFreeVarSet
    · apply Finset.sdiff_subset_sdiff
      · apply Finset.subset_biUnion_of_mem
        simp only [List.mem_toFinset]
        exact a1_left
      · apply Set.Subset.refl
  case not_ phi phi_ih =>
    simp only [Formula.close]
    simp only [Formula.freeVarSet]
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.close]
    simp only [Formula.freeVarSet]
    apply Finset.union_subset_diff
    · apply phi_ih
    · apply psi_ih
  case forall_ x phi phi_ih =>
    simp only [Formula.close]
    simp only [Formula.freeVarSet]
    apply phi_ih


--------------------------------------------------


-- 4.

lemma VarSubstFreeVarSet
  (z : String)
  (t : Var)
  (v : Var) :
  (Var.subst (Var.free_ z) t v).freeVarSet ⊆ t.freeVarSet ∪ v.freeVarSet \ {Var.free_ z} :=
  by
  cases v
  case free_ x =>
    simp only [Var.subst]
    split
    case isTrue c1 =>
      apply Finset.subset_union_left
    case isFalse c1 =>
      have s1 : Var.freeVarSet (free_ x) \ {free_ z} = {free_ x} :=
      by
        simp only [Var.freeVarSet]
        simp only [sdiff_eq_left, Finset.disjoint_singleton_left, Finset.mem_singleton]
        intro contra
        apply c1
        rewrite [contra]
        apply Eq.refl

      rewrite [s1]
      apply Finset.subset_union_right
  case bound_ i =>
    simp only [Var.subst]
    conv =>
      lhs
      simp only [Var.freeVarSet]
    apply Finset.empty_subset


lemma FormulaSubstFreeVarSet
  (z : String)
  (t : Var)
  (F : Formula) :
  (Formula.subst (Var.free_ z) t F).freeVarSet ⊆ t.freeVarSet ∪ F.freeVarSet \ {Var.free_ z} :=
  by
  induction F
  case pred_ X vs =>
    simp only [Formula.subst]
    simp only [Formula.freeVarSet]
    simp only [Finset.biUnion_subset_iff_forall_subset, List.mem_toFinset, List.mem_map, forall_exists_index]
    intro u v a1
    obtain ⟨a1_left, a1_right⟩ := a1
    rewrite [← a1_right]

    trans Var.freeVarSet t ∪ Var.freeVarSet v \ {free_ z}
    · apply VarSubstFreeVarSet
    · apply Finset.union_subset_union_right
      apply Finset.sdiff_subset_sdiff
      · apply Finset.subset_biUnion_of_mem
        simp only [List.mem_toFinset]
        exact a1_left
      · apply Set.Subset.refl
  case not_ phi phi_ih =>
    simp only [Formula.subst]
    simp only [Formula.freeVarSet]
    exact phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.subst]
    simp only [Formula.freeVarSet]
    apply Finset.union_subset_left_right_diff
    · exact phi_ih
    · exact psi_ih
  case forall_ x phi phi_ih =>
    simp only [Formula.subst]
    simp only [Formula.freeVarSet]
    exact phi_ih


--------------------------------------------------


lemma VarSubstFreeVarSet'
  (z : String)
  (t : Var)
  (v : Var) :
  v.freeVarSet \ {Var.free_ z} ⊆ (Var.subst (Var.free_ z) t v).freeVarSet :=
  by
  cases v
  case free_ x =>
    simp only [Var.subst]
    split
    case isTrue c1 =>
      rewrite [c1]
      conv =>
        lhs
        simp only [Var.freeVarSet]
      simp only [sdiff_self, Finset.bot_eq_empty, Finset.empty_subset]
    case isFalse c1 =>
      simp only [Var.freeVarSet]
      exact Finset.sdiff_subset
  case bound_ i =>
    conv =>
      lhs
      simp only [Var.freeVarSet]
    simp only [Finset.empty_sdiff, Finset.empty_subset]


lemma FormulaSubstFreeVarSet'
  (z : String)
  (t : Var)
  (F : Formula) :
  F.freeVarSet \ {Var.free_ z} ⊆ (Formula.subst (Var.free_ z) t F).freeVarSet :=
  by
  induction F
  case pred_ X vs =>
    simp only [Formula.subst]
    simp only [Formula.freeVarSet]

    induction vs
    case nil =>
      simp only [List.toFinset_nil, Finset.biUnion_empty, Finset.empty_sdiff, List.map_nil]
      apply Set.Subset.refl
    case cons hd tl ih =>
      simp only [List.toFinset_cons, Finset.biUnion_insert, List.map_cons]

      have s1 : (Var.freeVarSet hd ∪ Finset.biUnion (List.toFinset tl) Var.freeVarSet) \ {free_ z} = (Var.freeVarSet hd \ {free_ z}) ∪ ((Finset.biUnion (List.toFinset tl) Var.freeVarSet) \ {free_ z}) :=
      by
        apply Finset.union_sdiff_distrib
      rewrite [s1]

      apply Finset.union_subset_union
      · apply VarSubstFreeVarSet'
      · exact ih
  case not_ phi phi_ih =>
    simp only [Formula.subst]
    simp only [Formula.freeVarSet]
    exact phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.subst]
    simp only [Formula.freeVarSet]
    apply Finset.diff_union_subset
    · apply phi_ih
    · apply psi_ih
  case forall_ x phi phi_ih =>
    simp only [Formula.subst]
    simp only [Formula.freeVarSet]
    exact phi_ih


--------------------------------------------------


def str_fun_to_var_fun
  (σ : String → String) :
  Var → Var
  | free_ x => free_ (σ x)
  | bound_ i => bound_ i


lemma SubOpenVar
  (v : Var)
  (σ : String → String)
  (j : ℕ)
  (z : String)
  (h1 : σ z = z) :
  Var.substFun (str_fun_to_var_fun σ) (Var.open j (free_ z) v) =
    Var.open j (free_ z) (Var.substFun (str_fun_to_var_fun σ) v) :=
  by
  cases v
  case free_ x =>
    conv =>
      lhs
      simp only [Var.open]
      simp only [Var.substFun]
      simp only [str_fun_to_var_fun]
    apply Eq.refl
  case bound_ i =>
    conv =>
      lhs
      simp only [Var.open]
    split
    case isTrue c1 =>
      simp only [Var.substFun]
      simp only [Var.open]
      split
      case isTrue c2 =>
        apply Eq.refl
      case isFalse c2 =>
        contradiction
    case isFalse c1 =>
      split
      case isTrue c2 =>
        simp only [Var.substFun]
        simp only [str_fun_to_var_fun]
        simp only [Var.open]
        split
        case isTrue c3 =>
          contradiction
        case isFalse c3 =>
          rewrite [h1]
          apply Eq.refl
      case isFalse c2 =>
        simp only [Var.substFun]
        simp only [Var.open]
        split
        case isTrue c3 =>
          contradiction
        case isFalse c3 =>
          apply Eq.refl

/-
lemma SubCloseVar
  (v : Var)
  (σ : String → String)
  (y : String)
  (k : ℕ)
  (h1 : σ y = y)
  (h2 : ∀ (x : String), ¬ y = σ x) :
  Var.substFun (str_fun_to_var_fun σ) (Var.close k (free_ y) v) =
    Var.close (free_ y) k (Var.sub_Var (str_fun_to_var_fun σ) v) :=
  by
  cases v
  case free_ x =>
    simp only [closeVar]
    by_cases c1 : y = x
    · subst c1
      simp only [Var.sub_Var]
      simp only [str_fun_to_var_fun]
      simp only [h1]
      simp
    · simp
      simp only [if_neg c1]
      simp only [Var.sub_Var]
      simp only [str_fun_to_var_fun]
      specialize h2 x
      simp only [if_neg h2]
  case bound_ i =>
    simp only [closeVar]
    simp only [Var.sub_Var]


lemma SubOpenFormula
  (F : Formula)
  (σ : String → String)
  (k : ℕ)
  (x : String)
  (h1 : σ x = x) :
  Formula.sub_Var (str_fun_to_var_fun σ) (openFormulaAux k (free_ x) F) =
    openFormulaAux k (free_ x) (Formula.sub_Var (str_fun_to_var_fun σ) F) :=
  by
  induction F generalizing k
  case pred_ X vs =>
    simp only [openFormulaAux]
    simp only [Formula.sub_Var]
    simp
    simp only [List.map_eq_map_iff]
    intro v _
    exact SubOpenVar v σ k x h1
  case not_ phi phi_ih =>
    simp only [openFormulaAux]
    simp only [Formula.sub_Var]
    congr! 1
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [openFormulaAux]
    simp only [Formula.sub_Var]
    congr! 1
    · apply phi_ih
    · apply psi_ih
  case forall_ phi phi_ih =>
    simp only [openFormulaAux]
    simp only [Formula.sub_Var]
    congr! 1
    apply phi_ih


lemma SubCloseFormula
  (F : Formula)
  (σ : String → String)
  (x : String)
  (k : ℕ)
  (h1 : σ x = x)
  (h2 : ∀ (y : String), ¬ x = σ y) :
  Formula.sub_Var (str_fun_to_var_fun σ) (closeFormulaAux (free_ x) k F) = closeFormulaAux (free_ x) k (Formula.sub_Var (str_fun_to_var_fun σ) F) :=
  by
  induction F generalizing k
  case pred_ X vs =>
    simp only [closeFormulaAux]
    simp only [Formula.sub_Var]
    simp
    simp only [List.map_eq_map_iff]
    intro v _
    exact SubCloseVar v σ x k h1 h2
  case not_ phi phi_ih =>
    simp only [closeFormulaAux]
    simp only [Formula.sub_Var]
    congr! 1
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [closeFormulaAux]
    simp only [Formula.sub_Var]
    congr! 1
    · apply phi_ih
    · apply psi_ih
  case forall_ phi phi_ih =>
    simp only [closeFormulaAux]
    simp only [Formula.sub_Var]
    congr! 1
    apply phi_ih

--------------------------------------------------

theorem shift_sub_Var
  (D : Type)
  (σ : String → String)
  (V : VarAssignment D)
  (d : D) :
  shift D (V ∘ Var.sub_Var (str_fun_to_var_fun σ)) d =
    shift D V d ∘ Var.sub_Var (str_fun_to_var_fun σ) :=
  by
  funext v
  simp
  cases v
  case _ x =>
    simp only [Var.sub_Var]
    simp only [shift]
    simp only [str_fun_to_var_fun]
    simp
  case _ i =>
    cases i
    case zero =>
      simp only [Var.sub_Var]
      simp only [shift]
    case succ n =>
      simp only [Var.sub_Var]
      simp only [shift]
      simp


theorem HoldsIffSubHolds
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (σ : String → String)
  (F : Formula) :
  Holds D I (V ∘ (Var.sub_Var (str_fun_to_var_fun σ))) F ↔
    Holds D I V (Formula.sub_Var (str_fun_to_var_fun σ) F) :=
  by
  induction F generalizing V
  case pred_ X vs =>
    simp only [Formula.sub_Var]
    simp only [Holds]
    congr! 1
    simp
  case not_ phi phi_ih =>
    simp only [Formula.sub_Var]
    simp only [Holds]
    congr! 1
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.sub_Var]
    simp only [Holds]
    congr! 1
    · apply phi_ih
    · apply psi_ih
  case forall_ phi phi_ih =>
    simp only [Formula.sub_Var]
    simp only [Holds]
    apply forall_congr'
    intro d
    simp only [← phi_ih]
    congr!
    apply shift_sub_Var
-/
--------------------------------------------------


theorem ShiftVarOpenList
  (D : Type)
  (V : VarAssignment D)
  (j : ℕ)
  (zs : List String)
  (d : D) :
  shift D (V ∘ Var.openList j (List.map free_ zs)) d =
    shift D V d ∘ Var.openList (j + 1) (List.map free_ zs) :=
  by
  funext v
  simp only [Function.comp_apply]
  cases v
  case free_ x =>
    simp only [Var.openList]
    simp only [shift]
    simp only [Function.comp_apply]
    apply Eq.refl
  case bound_ i =>
    cases i
    case zero =>
      simp only [Var.openList]
      split
      case isTrue c1 =>
        simp only [shift]
      case isFalse c1 =>
        exfalso
        apply c1
        apply Nat.zero_lt_succ
    case succ i =>
      simp only [Var.openList]
      split
      case isTrue c1 =>
        simp only [Nat.succ_lt_succ_iff] at c1

        simp only [shift]
        simp only [Function.comp_apply]
        simp only [Var.openList]
        split
        case isTrue c2 =>
          apply Eq.refl
        case isFalse c2 =>
          contradiction
      case isFalse c1 =>
        simp only [Nat.succ_lt_succ_iff] at c1

        have s1 : i + 1 - (j + 1) = i - j :=
        by
          apply Nat.add_sub_add_right
        rewrite [s1]

        simp only [List.length_map, List.getElem_map]

        split
        case isTrue c2 =>
          simp only [shift]
          simp only [Function.comp_apply]
          simp only [Var.openList]
          split
          case isTrue c3 =>
            contradiction
          case isFalse c3 =>
            split
            case isTrue c4 =>
              simp only [List.getElem_map]
            case isFalse c4 =>
              simp only [List.length_map] at c4
              contradiction
        case isFalse c2 =>
          simp only [shift]
          simp only [Function.comp_apply]
          simp only [Var.openList]
          split
          case isTrue c3 =>
            contradiction
          case isFalse c3 =>
            split
            case isTrue c4 =>
              simp only [List.length_map] at c4
              contradiction
            case isFalse c4 =>
              simp only [List.length_map]
              simp only [Nat.add_eq]


lemma HoldsOpenList
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (j : Nat)
  (zs : List String)
  (F : Formula) :
  Holds D I (V ∘ Var.openList j (zs.map Var.free_)) F ↔
    Holds D I V (Formula.openList j (zs.map Var.free_) F) :=
  by
  induction F generalizing V j
  case pred_ X vs =>
    simp only [Holds]
    simp only [Formula.openList]
    simp only [Holds]
    congr! 1
    simp only [List.map_map]
  case not_ phi phi_ih =>
    simp only [Holds]
    congr! 1
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Holds]
    congr! 1
    · apply phi_ih
    · apply psi_ih
  case forall_ _ phi phi_ih =>
    simp only [Holds]
    apply forall_congr'
    intro d
    simp only [← phi_ih]
    congr!
    apply ShiftVarOpenList


--------------------------------------------------


theorem ShiftListVarOpenList
  (D : Type)
  (V : VarAssignment D)
  (xs : List String) :
  V ∘ Var.openList 0 (List.map free_ xs) =
    shiftList D V (List.map (V ∘ free_) xs) :=
  by
  induction xs
  case nil =>
    funext v
    simp only [List.map_nil, Function.comp_apply]
    simp only [shiftList]
    cases v
    case free_ x =>
      simp only [Var.openList]
    case bound_ i =>
      simp only [Var.openList]
      split
      case isTrue c1 =>
        apply Eq.refl
      case isFalse c1 =>
        split
        case isTrue c2 =>
          simp only [tsub_zero, List.length_nil, not_lt_zero] at c2
        case isFalse c2 =>
          simp only [tsub_zero, List.length_nil, add_zero]
  case cons hd tl ih =>
    funext v
    simp only [List.map_cons, Function.comp_apply]
    simp only [shiftList]
    cases v
    case free_ x =>
      simp only [shift]
      rewrite [← ih]
      simp only [Var.openList]
      simp only [Function.comp_apply]
      simp only [Var.openList]
    case bound_ i =>
      cases i
      case zero =>
        simp only [shift]
        simp only [Var.openList]
        split
        case isTrue c1 =>
          simp only [lt_self_iff_false] at c1
        case isFalse c1 =>
          split
          case isTrue c2 =>
            simp only [tsub_self, List.getElem_cons_zero]
          case isFalse c2 =>
            exfalso
            apply c2
            simp only [List.length_cons, List.length_map]
            simp only [tsub_self]
            apply Nat.zero_lt_succ
      case succ i =>
        simp only [shift]
        rewrite [← ih]
        simp only [Function.comp_apply]
        simp only [Var.openList]
        grind


lemma lc_at_iff_lc
  (F : Formula) :
  lc_at 0 F ↔ lc F :=
  by
  constructor
  · intro a1
    sorry
  · intro a1
    sorry


theorem HoldsCoincideVar
  (D : Type)
  (I : Interpretation D)
  (V V' : VarAssignment D)
  (F : Formula)
  (h1 : ∀ (v : Var), occursFreeIn v F → V v = V' v) :
  Holds D I V F ↔ Holds D I V' F :=
  by
  induction F generalizing V V'
  case pred_ X vs =>
    simp only [occursFreeIn] at h1

    simp only [Holds]
    congr! 1
    simp only [List.map_eq_map_iff]
    exact h1
  case not_ phi phi_ih =>
    simp only [occursFreeIn] at h1

    simp only [Holds]
    congr! 1
    apply phi_ih
    exact h1
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Holds]
    congr! 1
    · apply phi_ih
      intro v a1
      apply h1
      simp only [occursFreeIn]
      left
      exact a1
    · apply psi_ih
      intro v a1
      apply h1
      simp only [occursFreeIn]
      right
      exact a1
  case forall_ x phi phi_ih =>
    simp only [occursFreeIn] at h1

    simp only [Holds]
    apply forall_congr'
    intro d
    apply phi_ih
    intro v a1
    cases v
    case free_ x =>
      simp only [shift]
      apply h1
      exact a1
    case bound_ i =>
      cases i
      case zero =>
        simp only [shift]
      case succ i =>
        simp only [shift]
        apply h1
        simp only [lift]
        exact a1


lemma HoldsShift
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (F : Formula)
  (z : String)
  (h1 : ¬ occursFreeIn (free_ z) F) :
  (∀ (d : D), Holds D I (shift D V d) F) ↔ ∀ (d : D), Holds D I (Function.updateITE V (free_ z) d ∘ Var.openList 0 [free_ z]) F :=
  by
  apply forall_congr'
  intro d
  apply HoldsCoincideVar
  intro v a1
  simp only [Function.comp_apply]
  simp only [Function.updateITE]
  cases v
  case free_ x =>
    simp only [shift]
    simp only [Var.openList]
    split
    case isTrue c1 =>
      simp only [free_.injEq] at c1
      rewrite [← c1] at h1
      contradiction
    case isFalse c1 =>
      apply Eq.refl
  case bound_ i =>
    cases i
    case zero =>
      simp only [shift]
      simp only [Var.openList]
      simp only [List.length_cons, List.length_nil]
      grind
    case succ i =>
      simp only [shift]
      simp only [Var.openList]
      simp only [List.length_cons, List.length_nil]
      grind only


lemma HoldsForall
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (x : String)
  (F : Formula)
  (z : String)
  (h1 : ¬ occursFreeIn (free_ z) F) :
  Holds D I V (forall_ x F) ↔ ∀ (d : D), Holds D I (Function.updateITE V (free_ z) d) (Formula.openList 0 [free_ z] F) :=
  by
  simp only [Holds]
  simp only [HoldsShift D I V F z h1]
  apply forall_congr'
  intro d
  obtain s1 := HoldsOpenList D I (Function.updateITE V (free_ z) d) 0 [z] F
  simp only [List.map_cons, List.map_nil] at s1
  exact s1


theorem extracted_1
  (D : Type)
  (V : VarAssignment D)
  (j : ℕ)
  (z : String)
  (d : D) :
  shift D V d ∘ Var.close (j + 1) (free_ z) = shift D (V ∘ Var.close j (free_ z)) d :=
  by
  funext v
  simp only [Function.comp_apply]
  cases v
  case free_ x =>
    conv =>
      rhs
      simp only [shift]
      simp only [Function.comp_apply]
    simp only [Var.close]
    split
    case isTrue c1 =>
      simp only [shift]
    case isFalse c1 =>
      simp only [shift]
  case bound_ i =>
    cases i
    case zero =>
      conv =>
        rhs
        simp only [shift]
      simp only [Var.close]
      split
      case isTrue c1 =>
        simp only [shift]
      case isFalse c1 =>
        exfalso
        apply c1
        apply Nat.zero_lt_succ
    case succ i =>
      conv =>
        rhs
        simp only [shift]
        simp only [Function.comp_apply]
        simp only [Var.close]
      simp only [Var.close]
      split
      case isTrue c1 =>
        split
        case isTrue c2 =>
          simp only [shift]
        case isFalse c2 =>
          simp only [Nat.succ_lt_succ_iff] at c1
          contradiction
      case isFalse c1 =>
        simp only [Nat.succ_lt_succ_iff] at c1
        split
        case isTrue c2 =>
          contradiction
        case isFalse c2 =>
          simp only [shift]


lemma HoldsClose
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (z : String)
  (F : Formula)
  (j : ℕ)
  (h1 : ¬ occursIn (free_ z) F)
  (h2 : F.lc_at j) :
  Holds D I V F ↔ Holds D I (V ∘ Var.close j (free_ z)) (Formula.openList j [free_ z] F) :=
  by
  induction F generalizing V j
  case pred_ X vs =>
    simp only [occursIn] at h1
    simp only [Formula.lc_at] at h2

    simp only [Formula.openList]
    simp only [Holds]
    congr! 1
    simp only [List.map_map, List.map_inj_left, Function.comp_apply]
    intro v a1
    specialize h2 v a1
    cases v
    case free_ x =>
      simp only [Var.openList]
      simp only [Var.close]

      split
      case isTrue c1 =>
        simp only [free_.injEq] at c1
        rewrite [c1] at a1
        contradiction
      case isFalse c1 =>
        apply Eq.refl
    case bound_ i =>
      simp only [Var.lc_at] at h2

      simp only [Var.openList]
      simp only [List.length_cons, List.length_nil, List.getElem_singleton]
      split
      case isTrue c1 =>
        simp only [Var.close]
        split
        case isTrue c2 =>
          apply Eq.refl
        case isFalse c2 =>
          contradiction
      case isFalse c1 =>
        contradiction
  case not_ phi phi_ih =>
    simp only [occursIn] at h1
    simp only [Formula.lc_at] at h2

    simp only [Holds]
    congr! 1
    apply phi_ih
    · exact h1
    · exact h2
  case imp_ phi psi phi_ih psi_ih =>
    simp only [occursIn] at h1
    rewrite [not_or] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    simp only [Formula.lc_at] at h2
    obtain ⟨h2_left, h2_right⟩ := h2

    simp only [Holds]
    congr! 1
    · apply phi_ih
      · exact h1_left
      · exact h2_left
    · apply psi_ih
      · exact h1_right
      · exact h2_right
  case forall_ x phi phi_ih =>
    simp only [occursIn] at h1
    simp only [Formula.lc_at] at h2

    simp only [Formula.openList]
    simp only [Holds]
    apply forall_congr'
    intro d
    specialize phi_ih (shift D V d) (j + 1) h1 h2
    rewrite [phi_ih]
    congr! 1
    apply extracted_1


lemma Formula.OpenListLC
  (F : Formula)
  (j : ℕ)
  (zs : List String)
  (h1 : F.lc_at j) :
  Formula.openList j (zs.map free_) F = F :=
  by
  induction F generalizing j
  case pred_ X vs =>
    simp only [Formula.lc_at] at h1

    simp only [Formula.openList]
    congr
    apply List.fun_is_id_on_mem_imp_map_eq_self
    intro v a1
    specialize h1 v a1
    cases v
    case free_ x =>
      simp only [Var.openList]
    case bound_ i =>
      cases i
      case zero =>
        simp only [Var.lc_at] at h1
        simp only [Var.openList]
        split
        case isTrue c1 =>
          apply Eq.refl
        case isFalse c1 =>
          contradiction
      case succ i =>
        simp only [Var.lc_at] at h1
        simp only [Var.openList]
        split
        case isTrue c1 =>
          apply Eq.refl
        case isFalse c1 =>
          contradiction
  case not_ phi phi_ih =>
    simp only [Formula.lc_at] at h1

    simp only [Formula.openList]
    congr!
    apply phi_ih
    exact h1
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.lc_at] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    simp only [Formula.openList]
    congr!
    · apply phi_ih
      exact h1_left
    · apply psi_ih
      exact h1_right
  case forall_ x phi phi_ih =>
    simp only [Formula.lc_at] at h1

    simp only [Formula.openList]
    congr
    apply phi_ih
    exact h1


lemma lc_at_instantiate
  (F : Formula)
  (j : ℕ)
  (zs : List String) :
  Formula.lc_at j (Formula.openList j (zs.map Var.free_) F) ↔ Formula.lc_at (j + zs.length) F :=
  by
  induction F generalizing j zs
  case pred_ X vs =>
    simp only [Formula.openList]
    simp only [Formula.lc_at]
    constructor
    · intro a1 v a2
      specialize a1 (Var.openList j (List.map free_ zs) v)
      simp only [List.mem_map, forall_exists_index] at a1
      simp only [and_imp] at a1
      specialize a1 v a2

      cases v
      case free_ x =>
        simp only [Var.lc_at]
      case bound_ i =>
        simp only [Var.lc_at]
        simp only [forall_const] at a1
        simp only [Var.openList] at a1
        split at a1
        case isTrue c1 =>
          linarith
        case isFalse c1 =>
          split at a1
          case isTrue c2 =>
            simp only [List.length_map] at c2
            exact lt_add_of_tsub_lt_left c2
          case isFalse c2 =>
            simp only [Var.lc_at] at a1
            have s1 : i - j < (List.map free_ zs).length :=
            by
              linarith
            contradiction
    · intro a1 v a2
      cases v
      case free_ x =>
        simp only [Var.lc_at]
      case bound_ i =>
        simp only [Var.lc_at]
        simp only [List.mem_map] at a2
        obtain ⟨z, ⟨a2_left, a2_right⟩⟩ := a2

        specialize a1 z a2_left
        cases z
        case free_ x =>
          simp only [Var.openList] at a2_right
          contradiction
        case bound_ i' =>
          simp only [Var.lc_at] at a1
          simp only [Var.openList] at a2_right
          split at a2_right
          case isTrue c1 =>
            simp only [bound_.injEq] at a2_right
            rewrite [a2_right] at c1
            exact c1
          case isFalse c1 =>
            simp only [List.length_map, List.getElem_map] at a2_right
            split at a2_right
            case isTrue c2 =>
              contradiction
            case isFalse c2 =>
              exfalso
              apply c2
              omega
  case not_ phi phi_ih =>
    simp only [Formula.openList]
    simp only [Formula.lc_at]
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.openList]
    simp only [Formula.lc_at]
    congr! 1
    · apply phi_ih
    · apply psi_ih
  case forall_ _ phi phi_ih =>
    simp only [Formula.openList]
    simp only [Formula.lc_at]
    simp only [phi_ih]
    have s1 : j + 1 + List.length zs = j + List.length zs + 1 :=
    by
      linarith;
    rewrite [s1]
    apply Iff.refl


example
  (τ : String → ℕ → Formula)
  (j j' : ℕ)
  (zs zs' : List String)
  (F : Formula) :
  predSub τ (Formula.openList j (zs.map free_) F) = Formula.openList j' (zs'.map free_) (predSub τ F) :=
  by
  induction F generalizing j j'
  case pred_ X vs =>
    simp only [predSub]
    sorry
  case forall_ x phi phi_ih =>
    simp only [predSub]
    simp only [Formula.openList]
    simp only [predSub]
    congr
    apply phi_ih
  all_goals
    sorry


example
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (τ : String → ℕ → Formula)
  (F : Formula)
  (h1 : F.lc) :
  Holds D I V (F.predSub τ) ↔
    Holds D (Interpretation.usingPred D I fun (X : String) (ds : List D) => Holds D I (shiftList D V ds) (τ X ds.length)) V F :=
  by
  induction h1 generalizing V
  case pred_ X vs ih =>
    simp only [predSub]
    simp only [Interpretation.usingPred]
    simp only [Holds]
    simp only [List.length_map]

    have s1 : ∀ (v : Var), v ∈ vs → Var.lc_at 0 v :=
    by
      intro v a1
      specialize ih v a1
      cases v
      case free_ x =>
        simp only [Var.lc_at]
      case bound_ i =>
        simp only [Var.isFree] at ih

    obtain s2 := free_var_list_to_string_list vs s1
    obtain ⟨zs, s2⟩ := s2

    obtain s3 := HoldsOpenList D I V 0 zs (τ X (List.length vs))
    rewrite [← s2] at s3
    rewrite [← s3]

    congr! 1
    rewrite [s2]
    simp only [List.map_map]
    simp only [ShiftListVarOpenList]
  case forall_ x phi z ih_1 ih_2 =>
    simp only [← lc_at_iff_lc] at ih_1

    simp only [predSub]

    obtain s1 := lc_at_instantiate phi 0 [z]
    simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at s1
    rewrite [s1] at ih_1

    simp only [Holds]
    apply forall_congr'
    intro d

    obtain s1 := HoldsForall D I V x (predSub τ phi) z
    simp only [Holds] at s1

    obtain s2 := ShiftListVarOpenList D V [z]
    simp only [List.map_cons, List.map_nil, Function.comp_apply] at s2

    obtain s3 := Formula.OpenListLC phi 1 [z] ih_1
    simp only [List.map_cons, List.map_nil] at s3

    obtain s4 := HoldsClose D I V z

    sorry
  all_goals
    sorry


end LN
