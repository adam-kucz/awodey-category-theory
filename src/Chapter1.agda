{-# OPTIONS --safe --exact-split #-}
module Chapter1 where

open import Universes hiding (A; B)
open import Type.Identity
open import Logic

-- Definition 1.1
record Category (𝒰 𝒱 : Universe) : 𝒰 ⁺ ⊔ 𝒱 ⁺ ˙ where
  infixl 165 _∘_ _∘_-cond
  field
    obj : 𝒰 ˙
    arr : 𝒱 ˙
    dom cod : arr → obj
    _∘_ : arr → arr → arr
    𝟙 : obj → arr
    
  _∘_-cond : arr → arr → 𝒰 ˙
  g ∘ f -cond = cod f == dom g

  field
    assoc : ∀ h g f
      ⦃ hg : h ∘ g -cond ⦄
      ⦃ gf : g ∘ f -cond ⦄
      → ------------------------------
      h ∘ (g ∘ f) == (h ∘ g) ∘ f
    unit : ∀ f →
      let A = dom f; B = cod f
      in f ∘ 𝟙 A == f ∧ 𝟙 B ∘ f == f

  _∶_⟶_ : (f : arr)(A B : obj) → 𝒰 ˙
  f ∶ A ⟶ B = A == dom f ∧ B == cod f

  ∃-arr-bind : (A B : obj)(X : arr → 𝒲 ˙) → 𝒰 ⊔ 𝒱 ⊔ 𝒲 ˙
  ∃-arr-bind A B X = ∃ λ f → f ∶ A ⟶ B ∧ X f

  syntax ∃-arr-bind A B (λ f → X) = ∃[ f ∶ A ⟶ B ]→ X

open Category ⦃ … ⦄ hiding (obj; arr)
open Category using (obj; arr)

-- Definition 1.2
record Functor (C : Category 𝒰 𝒱)(D : Category 𝒲 𝒳)
       : 𝒰 ⊔ 𝒲 ⊔ 𝒱 ⊔ 𝒳 ˙ where
  private instance _ = C; _ = D
  field
    F₀ : obj C → obj D
    F₁ : arr C → arr D
    dom-preserv : ∀ f → dom (F₁ f) == F₀ (dom f)
    cod-preserv : ∀ f → cod (F₁ f) == F₀ (cod f)
    𝟙-preserv : ∀ A → F₁ (𝟙 A) == 𝟙 (F₀ A)
    ∘-preserv : ∀ g f ⦃ gf : g ∘ f -cond ⦄ → F₁ (g ∘ f) == F₁ g ∘ F₁ f

  open import Proof
  F∘F-cond : ∀ {g f} ⦃ gf : g ∘ f -cond ⦄ → F₁ g ∘ F₁ f -cond
  F∘F-cond {g = g}{f} ⦃ gf ⦄ =
    proof cod (F₁ f)
      === F₀ (cod f) :by: cod-preserv f
      === F₀ (dom g) :by: ap F₀ gf 
      === dom (F₁ g) :by: sym $ dom-preserv g
    qed

module WithCategory (C : Category 𝒰 𝒱) where
  private instance ℂ = C
  
  -- Definition 1.3
  infix 150 _is-isomorphism
  _is-isomorphism : (f : arr C) → 𝒰 ⊔ 𝒱 ˙
  f is-isomorphism = ∃ λ (g : arr C) →
    (f ∘ g -cond ∧ g ∘ f -cond) ∧
    (g ∘ f == 𝟙 A ∧ f ∘ g == 𝟙 B)
    where A = dom f
          B = cod f

  _≅_ : (A B : obj C) → 𝒰 ⊔ 𝒱 ˙
  A ≅ B = ∃[ f ∶ A ⟶ B ]→ f is-isomorphism
