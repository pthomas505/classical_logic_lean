import ClassicalLogicLean.LN.Formula
import ClassicalLogicLean.LN.OpenClose
import ClassicalLogicLean.LN.Semantics


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


namespace LN

open Var Formula


def Var.sub_Var (σ : Var → Var) : Var → Var
  | free_ x => σ (free_ x)
  | bound_ i => bound_ i


def Formula.sub_Var (σ : Var → Var) : Formula → Formula
  | pred_ X vs => pred_ X (vs.map (Var.sub_Var σ))
  | not_ phi => not_ (phi.sub_Var σ)
  | imp_ phi psi => imp_ (phi.sub_Var σ) (psi.sub_Var σ)
  | forall_ x phi => forall_ x (phi.sub_Var σ)

--------------------------------------------------

def Var.sub_Str (σ : String → String) : Var → Var
  | free_ x => free_ (σ x)
  | bound_ i => bound_ i


def Formula.sub_Str (σ : String → String) : Formula → Formula
  | pred_ X vs => pred_ X (vs.map (Var.sub_Str σ))
  | not_ phi => not_ (phi.sub_Str σ)
  | imp_ phi psi => imp_ (phi.sub_Str σ) (psi.sub_Str σ)
  | forall_ x phi => forall_ x (phi.sub_Str σ)

--------------------------------------------------

def str_fun_to_var_fun
  (σ : String → String) :
  Var → Var
  | free_ x => free_ (σ x)
  | bound_ i => bound_ i


lemma SubOpenVar
  (v : Var)
  (σ : String → String)
  (k : ℕ)
  (y : String)
  (h1 : σ y = y) :
  Var.sub_Var (str_fun_to_var_fun σ) (openVar k (free_ y) v) =
    openVar k (free_ y) (Var.sub_Var (str_fun_to_var_fun σ) v) :=
  by
  cases v
  case free_ x =>
    simp only [openVar]
    simp only [Var.sub_Var]
    simp only [str_fun_to_var_fun]
  case bound_ i =>
    simp only [openVar]
    split
    case isTrue c1 =>
      simp only [Var.sub_Var]
      simp only [str_fun_to_var_fun]
      rewrite [h1]
      split
      case isTrue c2 =>
        apply Eq.refl
      case isFalse c2 =>
        contradiction
    case isFalse c1 =>
      simp only [Var.sub_Var]
      split
      case isTrue c2 =>
        contradiction
      case isFalse c2 =>
        apply Eq.refl


lemma SubCloseVar
  (v : Var)
  (σ : String → String)
  (y : String)
  (k : ℕ)
  (h1 : σ y = y) :
  -- (h2 : ∀ (x : String), ¬ y = σ x) :
  Var.sub_Var (str_fun_to_var_fun σ) (closeVar (free_ y) k v) =
    closeVar (free_ y) k (Var.sub_Var (str_fun_to_var_fun σ) v) :=
  by
  cases v
  case free_ x =>
    rewrite [closeVar]
    split
    case isTrue c1 =>
      rewrite [c1]
      simp only [Var.sub_Var]
      simp only [str_fun_to_var_fun]
      rewrite [closeVar]
      split
      case isTrue c2 =>
        apply Eq.refl
      case isFalse c2 =>
        simp only [free_.injEq] at c1
        simp only [free_.injEq] at c2
        rewrite [c1] at h1
        rewrite [h1] at c2
        contradiction
    case isFalse c1 =>
      simp only [Var.sub_Var]
      simp only [str_fun_to_var_fun]
      rewrite [closeVar]
      split
      case isTrue c2 =>
        simp only [free_.injEq] at c1
        simp only [free_.injEq] at c2
        sorry
      case isFalse c2 =>
        apply Eq.refl
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
    simp only [List.map_map]
    simp only [openFormulaAux]
    congr 1
    simp only [List.map_map, List.map_inj_left, Function.comp_apply]
    intro v a1
    apply SubOpenVar
    exact h1
  case not_ phi phi_ih =>
    simp only [openFormulaAux]
    simp only [Formula.sub_Var]
    congr 1
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [openFormulaAux]
    simp only [Formula.sub_Var]
    congr 1
    · apply phi_ih
    · apply psi_ih
  case forall_ phi phi_ih =>
    simp only [openFormulaAux]
    simp only [Formula.sub_Var]
    congr 1
    apply phi_ih


lemma SubCloseFormula
  (F : Formula)
  (σ : String → String)
  (x : String)
  (k : ℕ)
  (h1 : σ x = x) :
  -- (h2 : ∀ (y : String), ¬ x = σ y) :
  Formula.sub_Var (str_fun_to_var_fun σ) (closeFormulaAux (free_ x) k F) = closeFormulaAux (free_ x) k (Formula.sub_Var (str_fun_to_var_fun σ) F) :=
  by
  induction F generalizing k
  case pred_ X vs =>
    simp only [closeFormulaAux]
    simp only [Formula.sub_Var]
    simp only [closeFormulaAux]
    congr 1
    simp only [List.map_map, List.map_inj_left, Function.comp_apply]
    intro v a1
    apply SubCloseVar
    exact h1
  case not_ phi phi_ih =>
    simp only [closeFormulaAux]
    simp only [Formula.sub_Var]
    congr 1
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [closeFormulaAux]
    simp only [Formula.sub_Var]
    congr 1
    · apply phi_ih
    · apply psi_ih
  case forall_ phi phi_ih =>
    simp only [closeFormulaAux]
    simp only [Formula.sub_Var]
    congr 1
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
  simp only [Function.comp_apply]
  cases v
  case free_ x =>
    simp only [Var.sub_Var]
    simp only [str_fun_to_var_fun]
    simp only [shift]
    simp only [Function.comp_apply]
    simp only [Var.sub_Var]
    simp only [str_fun_to_var_fun]
  case bound_ i =>
    cases i
    case zero =>
      simp only [Var.sub_Var]
      simp only [shift]
    case succ n =>
      simp only [Var.sub_Var]
      simp only [shift]
      simp only [Function.comp_apply]
      simp only [Var.sub_Var]


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
    simp only [List.map_map]
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
    rewrite [← phi_ih]
    congr!
    apply shift_sub_Var


end LN
