import ClassicalLogicLean.NV.Semantics
import ClassicalLogicLean.NV.Sub.Var.All.Rec.ReplaceFree


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


namespace FOL.NV.Sub.Var.All.Ind

open Formula_


/--
  Helper definition for `is_sub_var_all_ind`.
-/
inductive is_sub_var_all_ind_aux :
  (VarName_ → VarName_) →
  Finset VarName_ →
  Formula_ → Formula_ → Prop

  | pred_const_
    (σ : VarName_ → VarName_)
    (binders : Finset VarName_)
    (X : PredName_)
    (xs : List VarName_) :
    (∀ v : VarName_, v ∈ xs → v ∉ binders → σ v ∉ binders) →
    is_sub_var_all_ind_aux σ binders (pred_const_ X xs) (pred_const_ X (xs.map σ))

  | pred_var_
    (σ : VarName_ → VarName_)
    (binders : Finset VarName_)
    (X : PredName_)
    (xs : List VarName_) :
    (∀ v : VarName_, v ∈ xs → v ∉ binders → σ v ∉ binders) →
    is_sub_var_all_ind_aux σ binders (pred_var_ X xs) (pred_var_ X (xs.map σ))

  | eq_
    (σ : VarName_ → VarName_)
    (binders : Finset VarName_)
    (x y : VarName_) :
    (∀ v : VarName_, (v = x ∨ v = y) → v ∉ binders → σ v ∉ binders) →
    is_sub_var_all_ind_aux σ binders (eq_ x y) (eq_ (σ x) (σ y))

  | true_
    (σ : VarName_ → VarName_)
    (binders : Finset VarName_) :
    is_sub_var_all_ind_aux σ binders true_ true_

  | false_
    (σ : VarName_ → VarName_)
    (binders : Finset VarName_) :
    is_sub_var_all_ind_aux σ binders false_ false_

  | not_
    (σ : VarName_ → VarName_)
    (binders : Finset VarName_)
    (phi : Formula_)
    (phi' : Formula_) :
    is_sub_var_all_ind_aux σ binders phi phi' →
    is_sub_var_all_ind_aux σ binders phi.not_ phi'.not_

  | imp_
    (σ : VarName_ → VarName_)
    (binders : Finset VarName_)
    (phi psi : Formula_)
    (phi' psi' : Formula_) :
    is_sub_var_all_ind_aux σ binders phi phi' →
    is_sub_var_all_ind_aux σ binders psi psi' →
    is_sub_var_all_ind_aux σ binders (phi.imp_ psi) (phi'.imp_ psi')

  | and_
    (σ : VarName_ → VarName_)
    (binders : Finset VarName_)
    (phi psi : Formula_)
    (phi' psi' : Formula_) :
    is_sub_var_all_ind_aux σ binders phi phi' →
    is_sub_var_all_ind_aux σ binders psi psi' →
    is_sub_var_all_ind_aux σ binders (phi.and_ psi) (phi'.and_ psi')

  | or_
    (σ : VarName_ → VarName_)
    (binders : Finset VarName_)
    (phi psi : Formula_)
    (phi' psi' : Formula_) :
    is_sub_var_all_ind_aux σ binders phi phi' →
    is_sub_var_all_ind_aux σ binders psi psi' →
    is_sub_var_all_ind_aux σ binders (phi.or_ psi) (phi'.or_ psi')

  | iff_
    (σ : VarName_ → VarName_)
    (binders : Finset VarName_)
    (phi psi : Formula_)
    (phi' psi' : Formula_) :
    is_sub_var_all_ind_aux σ binders phi phi' →
    is_sub_var_all_ind_aux σ binders psi psi' →
    is_sub_var_all_ind_aux σ binders (phi.iff_ psi) (phi'.iff_ psi')

  | forall_
    (σ : VarName_ → VarName_)
    (binders : Finset VarName_)
    (x : VarName_)
    (phi phi' : Formula_) :
    is_sub_var_all_ind_aux (Function.updateITE σ x x) (binders ∪ {x}) phi phi' →
    is_sub_var_all_ind_aux σ binders (forall_ x phi) (forall_ x phi')

  | exists_
    (σ : VarName_ → VarName_)
    (binders : Finset VarName_)
    (x : VarName_)
    (phi phi' : Formula_) :
    is_sub_var_all_ind_aux (Function.updateITE σ x x) (binders ∪ {x}) phi phi' →
    is_sub_var_all_ind_aux σ binders (exists_ x phi) (exists_ x phi')

  | def_
    (σ : VarName_ → VarName_)
    (binders : Finset VarName_)
    (X : DefName_)
    (xs : List VarName_) :
    (∀ v : VarName_, v ∈ xs → v ∉ binders → σ v ∉ binders) →
    is_sub_var_all_ind_aux σ binders (def_ X xs) (def_ X (xs.map σ))


/--
  `is_sub_var_all_ind σ F F'` := True if and only if `F'` is the result of the simultaneous replacement of each free occurrence of any variable `v` in the formula `F` by a free occurrence of `σ v`.
-/
def is_sub_var_all_ind (σ : VarName_ → VarName_) (F F' : Formula_) : Prop := is_sub_var_all_ind_aux σ ∅ F F'


theorem substitution_theorem_is_sub_var_all_ind_aux
  (D : Type)
  (I : Interpretation_ D)
  (V V' : Valuation_ D)
  (E : Env_)
  (σ : VarName_ → VarName_)
  (binders : Finset VarName_)
  (F F' : Formula_)
  (h1 : is_sub_var_all_ind_aux σ binders F F')
  (h2 : ∀ v : VarName_, v ∈ binders → V v = V' (σ v))
  (h3 : ∀ v : VarName_, σ v ∉ binders → V v = V' (σ v))
  (h4 : ∀ v : VarName_, v ∈ binders → v = σ v) :
  holds D I V E F ↔ holds D I V' E F' :=
  by
  induction h1 generalizing V V'
  case pred_const_ σ' binders' X' xs' ih_1 | pred_var_ σ' binders' X' xs' ih_1 =>
    simp only [holds]
    simp only [List.map_map]
    congr! 1
    simp only [List.map_eq_map_iff]
    intro x a1
    simp only [Function.comp_apply]
    by_cases c1 : x ∈ binders'
    · exact h2 x c1
    · apply h3
      exact ih_1 x a1 c1
  case eq_ σ' binders' x y ih_1 =>
    simp only [holds]
    congr! 1
    · by_cases c1 : x ∈ binders'
      · exact h2 x c1
      · apply h3
        apply ih_1
        · left
          apply Eq.refl
        · exact c1
    · by_cases c1 : y ∈ binders'
      · exact h2 y c1
      · apply h3
        apply ih_1
        · right
          apply Eq.refl
        · exact c1
  case true_ | false_ =>
    simp only [holds]
  case not_ σ' binders' phi phi' _ ih_2 =>
    simp only [holds]
    congr! 1
    exact ih_2 V V' h2 h3 h4
  case
      imp_ σ' binders' phi psi phi' psi' _ _ phi_ih_2 psi_ih_2
    | and_ σ' binders' phi psi phi' psi' _ _ phi_ih_2 psi_ih_2
    | or_ σ' binders' phi psi phi' psi' _ _ phi_ih_2 psi_ih_2
    | iff_ σ' binders' phi psi phi' psi' _ _ phi_ih_2 psi_ih_2 =>
    simp only [holds]
    congr! 1
    · exact phi_ih_2 V V' h2 h3 h4
    · exact psi_ih_2 V V' h2 h3 h4
  case forall_ σ' binders' x phi phi' _ ih_2 | exists_ σ' binders' x phi phi' _ ih_2 =>
    simp only [Finset.union_singleton, Finset.mem_insert] at ih_2

    have s1 : ∀ (v : VarName_), ¬ v = x → v ∈ binders' → ¬ σ' v = x :=
    by
      intro v a1 a2 contra
      apply a1
      simp only [← contra]
      exact h4 v a2

    simp only [holds]
    first | apply forall_congr'| apply exists_congr
    intro d

    apply ih_2
    · intro v a1
      simp only [Function.updateITE]
      split
      case isTrue c1 =>
        split
        case isTrue c2 =>
          apply Eq.refl
        case isFalse c2 =>
          contradiction
      case isFalse c2 =>
        cases a1
        case inl a1 =>
          contradiction
        case inr a1 =>
          split
          case isTrue c3 =>
            exfalso
            exact s1 v c2 a1 c3
          case isFalse c3 =>
            exact h2 v a1
    · intro v a1
      simp only [Function.updateITE] at a1
      rewrite [not_or] at a1
      obtain ⟨a1_left, a1_right⟩ := a1

      simp only [Function.updateITE]
      split
      case isTrue c1 =>
        split
        case isTrue c2 =>
          apply Eq.refl
        case isFalse c2 =>
          contradiction
      case isFalse c1 =>
        split
        case isTrue c2 =>
          exfalso
          apply a1_left
          split
          case isTrue c3 =>
            contradiction
          case isFalse c3 =>
            exact c2
        case isFalse c2 =>
          split at a1_right
          case isTrue c3 =>
            contradiction
          case isFalse c3 =>
            apply h3
            exact a1_right
    · intro v a1
      simp only [Function.updateITE]
      split
      case isTrue c1 =>
        exact c1
      case isFalse c1 =>
        cases a1
        case inl a1 =>
          contradiction
        case inr a1 =>
          apply h4
          exact a1
  case def_ σ' binders' X' xs' ih_1 =>
    induction E
    case nil =>
      simp only [holds]
    case cons hd tl ih =>
      simp only [holds]
      split
      case isTrue c1 =>
        split
        case isTrue c2 =>
          simp only [List.map_map]
          apply holds_coincide_var
          intro v a1

          have s1 : List.map V xs' = List.map (V' ∘ σ') xs' :=
          by
            simp only [List.map_eq_map_iff]
            intro x a2
            by_cases c3 : x ∈ binders'
            · exact h2 x c3
            · apply h3
              exact ih_1 x a2 c3

          simp only [s1]
          apply Function.updateFromPairOfListsITE_mem_eq_len
          · simp only [var_is_free_in_iff_mem_free_var_set] at a1
            obtain s2 := hd.h1 a1
            simp only [List.mem_toFinset] at s2
            exact s2
          · simp only [List.length_map] at c2
            simp only [List.length_map]
            tauto
        case isFalse c2 =>
          simp only [List.length_map] at c2
          contradiction
      case isFalse c1 =>
        split
        case isTrue c2 =>
          simp only [List.length_map] at c2
          contradiction
        case isFalse c2 =>
          exact ih


theorem substitution_theorem_is_sub_var_all_ind
  (D : Type)
  (I : Interpretation_ D)
  (V : Valuation_ D)
  (E : Env_)
  (σ : VarName_ → VarName_)
  (F F' : Formula_)
  (h1 : is_sub_var_all_ind σ F F') :
  holds D I (V ∘ σ) E F ↔ holds D I V E F' :=
  by
  apply substitution_theorem_is_sub_var_all_ind_aux D I (V ∘ σ) V E σ ∅ F F' h1
  · simp
  · simp
  · simp


theorem substitution_is_valid_is_sub_var_all_ind
  (σ : VarName_ → VarName_)
  (F F' : Formula_)
  (h1 : is_sub_var_all_ind σ F F')
  (h2 : F.is_valid) :
  F'.is_valid :=
  by
  simp only [is_valid] at h2

  simp only [is_valid]
  intro D I V E
  simp only [← substitution_theorem_is_sub_var_all_ind D I V E σ F F' h1]
  apply h2


#lint
