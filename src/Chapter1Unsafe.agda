{-# OPTIONS --exact-split #-}
module Chapter1Unsafe where

open import Chapter1

open import Universes hiding (A)
open import Type.Decidable
open import Type.Identity hiding (refl)

open import Axiom.FunctionExtensionality
open import Axiom.ExcludedMiddle

-- 1.4.1 Example: Set & Set-fin
open import Type.Sum
open import Function
open import Logic
open import Proof

private
  Set-arr : (𝒰 ⁺) ˙
  Set-∘ : Set-arr {𝒰} → Set-arr → Set-arr

Set-arr {𝒰} = Σ λ (X : 𝒰 ˙) → Σ λ (Y : 𝒰 ˙) → X → Y
Set-∘ (Y₁ , (Z , g))(X , (Y₀ , f)) with excluded-middle (Y₀ == Y₁)
... | true (Id.refl Y) = X , (Z , g ∘ f)
... | false _ = X , (X , id)

SetC : ∀ 𝒰 → Category (𝒰 ⁺) (𝒰 ⁺)
Category.obj (SetC 𝒰) = 𝒰 ˙
Category.arr (SetC 𝒰) = Set-arr
Category.dom (SetC 𝒰) (X , _) = X
Category.cod (SetC 𝒰) (_ , (Y , _)) = Y
Category._∘_ (SetC 𝒰) = Set-∘
Category.𝟙 (SetC 𝒰) X = X , (X , id)
Category.assoc (SetC 𝒰) (Z₁ , (W , h))(Y₁ , (Z₀ , g))(X , (Y₀ , f))
  with excluded-middle (Y₀ == Y₁)
... | false ¬p = ⊥-recursion _ $ ¬p from-instance
... | true (Id.refl Y) with excluded-middle (Z₀ == Z₁)
... | false ¬p = ⊥-recursion _ $ ¬p from-instance
... | true (Id.refl Z) with excluded-middle (Y == Y)
... | true (Id.refl Y) = Id.refl (X , (W , h ∘ g ∘ f))
... | false ¬p = ⊥-recursion _ $ ¬p $ refl Y
∧left (Category.unit (SetC 𝒰) f-full@(X , (Y , f)))
  with excluded-middle (X == X)
... | true (Id.refl X) = refl f-full
... | false ¬p = ⊥-recursion _ $ ¬p $ refl X
∧right (Category.unit (SetC 𝒰) f-full@(X , (Y , f)))
  with excluded-middle (Y == Y)
... | true (Id.refl Y) = refl f-full
... | false ¬p = ⊥-recursion _ $ ¬p $ refl Y

open import Type.Finite
open import Operation.Binary

private
  SetFin-arr : (𝒰 ⁺) ˙
  SetFin-∘ : ClosedOp (SetFin-arr {𝒰})

SetFin-arr {𝒰} =
  Σ λ (Fin₀ : Finite 𝒰) → Σ λ (Fin₁ : Finite 𝒰) → elem Fin₀ → elem Fin₁
SetFin-∘ (Y₁ , (Z , g))(X , (Y₀ , f))
  with excluded-middle (elem Y₀ == elem Y₁)
... | true (Id.refl Y) = X , (Z , g ∘ f)
... | false _ = X , (X , id)

SetFin : ∀ 𝒰 → Category (𝒰 ⁺) (𝒰 ⁺)
Category.obj (SetFin 𝒰) = Finite 𝒰
Category.arr (SetFin 𝒰) = SetFin-arr
Category.dom (SetFin 𝒰) (X , _) = X
Category.cod (SetFin 𝒰) (_ , (Y , _)) = Y
Category._∘_ (SetFin 𝒰) = SetFin-∘
Category.𝟙 (SetFin 𝒰) X = (X , (X , id))
Category.assoc (SetFin 𝒰) (Z₁ , (W , h))(Y₁ , (Z₀ , g))(X , (Y₀ , f))
  with excluded-middle (elem Y₀ == elem Y₁)
... | false ¬p = ⊥-recursion _ $ ¬p $ ap ∧left from-instance
... | true (Id.refl Y) with excluded-middle (elem Z₀ == elem Z₁)
... | false ¬p = ⊥-recursion _ $ ¬p $ ap ∧left from-instance
... | true (Id.refl Z) with excluded-middle (Y == Y)
... | true (Id.refl Y) = Id.refl (X , (W , h ∘ g ∘ f))
... | false ¬p = ⊥-recursion _ $ ¬p $ refl Y
∧left (Category.unit (SetFin 𝒰) f-full@(X , (Y , f)))
  with excluded-middle (elem X == elem X)
... | true (Id.refl .(elem X)) = refl f-full
... | false ¬p = ⊥-recursion _ $ ¬p $ ap ∧left $ refl X
∧right (Category.unit (SetFin 𝒰) f-full@(X , (Y , f)))
  with excluded-middle (elem Y == elem Y)
... | true (Id.refl .(elem Y)) = refl f-full
... | false ¬p = ⊥-recursion _ $ ¬p $ ap ∧left $ refl Y

open import Relation.Binary

record Poset (𝒰 𝒱 : Universe) : 𝒰 ⁺ ⊔ 𝒱 ⁺ ˙ where
  field
    A : 𝒰 ˙
    ≤ : BinRel 𝒱 A
    ⦃ partial-order ⦄ : FormPartialOrder ≤

private
  Poset-arr : 𝒰 ⁺ ⊔ 𝒱 ⁺ ˙
  Poset-∘ : ClosedOp (Poset-arr {𝒰}{𝒱})

Poset-arr {𝒰}{𝒱} =
  Σ λ (X : Poset 𝒰 𝒱) → Σ λ (Y : Poset 𝒰 𝒱) →
  Σ λ (f : Poset.A X → Poset.A Y) → is-monotone (Poset.≤ X) (Poset.≤ Y) f
Poset-∘ (Y₁ , (Z , (g , g-mon))) (X , (Y₀ , (f , f-mon)))
  with excluded-middle (Poset.A Y₀ == Poset.A Y₁)
... | false _ = X , (X , (id , id))
... | true (Id.refl Y) with excluded-middle (Poset.≤ Y₀ == Poset.≤ Y₁)
... | true (Id.refl ≤) = X , (Z , (g ∘ f , g-mon ∘ f-mon))
... | false _ = X , (X , (id , id))

Pos : ∀ 𝒰 𝒱 → Category (𝒰 ⁺ ⊔ 𝒱 ⁺) (𝒰 ⁺ ⊔ 𝒱 ⁺)
Category.obj (Pos 𝒰 𝒱) = Poset 𝒰 𝒱
Category.arr (Pos 𝒰 𝒱) = Poset-arr {𝒰}{𝒱}
Category.dom (Pos 𝒰 𝒱) = pr₁
Category.cod (Pos 𝒰 𝒱) = pr₁ ∘ pr₂
Category._∘_ (Pos 𝒰 𝒱) = Poset-∘
Category.𝟙 (Pos 𝒰 𝒱) X = X , (X , (id , id))
Category.assoc (Pos 𝒰 𝒱) = {!!}
Category.unit (Pos 𝒰 𝒱) = {!!}
