-- Constructive Provability Logic 
-- The minimal, modal, propositional fragment
-- Robert J. Simmons, Bernardo Toninho

-- Alternate □E rule
{-# OPTIONS --no-positivity-check #-}

module AltBoxE where
open import Prelude
open import Accessibility.Inductive
open import Accessibility.IndexedList

module CORE (UWF : UpwardsWellFounded) where 
   open UpwardsWellFounded UWF
   open ILIST UWF

   -- Types/Propositions
   infixr 10 _⊃_
   data Type : Set where
      a   : (N : String) → Type
      _⊃_ : (A B : Type) → Type
      □   : (A : Type) → Type
      ◇   : (A : Type) → Type
      ¬□  : (A : Type) → Type
      ¬◇  : (A : Type) → Type

   -- Contexts
   Ctx = List Type
   MCtx = IList Type

   -- Natural deduction (restricted to just the hyp rule and rules for □A)
   infix 1 _⊢_[_]
   data _⊢_[_] : MCtx → Type → W → Set where
      hyp : ∀{A Γ w}
         → A at w ∈ Γ
         → Γ ⊢ A [ w ]
      □I : ∀{Γ A w}
         → (∀{w'} → w ≺ w' → Γ ⊢ A [ w' ])
         → Γ ⊢ □ A [ w ]
      □E' : ∀{Γ A C w w'} 
         → Γ ⊢ □ A [ w ]
         → w ≺ w' 
         → (Γ ⊢ A [ w' ] → Γ ⊢ C [ w ])
         → Γ ⊢ C [ w ] 

   Enumerable≺ : Set
   Enumerable≺ = ((w : W) → 
      Σ[ succ :: List W ] 
      (∀{w'} → w ≺ w' → w' ∈ succ) 
      × (∀{w'} → w' ∈ succ → w ≺ w'))

   □E : Enumerable≺
         → ∀{w Γ A C} 
         → Γ ⊢ □ A [ w ]
         → ((∀{w'} → w ≺ w' → Γ ⊢ A [ w' ]) → Γ ⊢ C [ w ])
         → Γ ⊢ C [ w ]
   □E enum≺ {w} {Γ} {A} {C} D D'' with enum≺ w
   ... | succ , all-succ , only-succ = iter succ (λ x → x) (λ x → Inl x)
    where
      iter : (succ' : List W) 
         → LIST.SET.Sub succ' succ
         → (∀{w'} → w' ∈ succ → (w' ∈ succ') + (Γ ⊢ A [ w' ]))
         → Γ ⊢ C [ w ] 
      iter [] sub col = 
         D'' (λ ω → case (col (all-succ ω)) (λ ()) (λ x → x))
      iter (w' :: succ') sub col = 
         □E' D (only-succ (sub Z))
          (λ D' → iter succ' (sub o LIST.SET.sub-cons) 
           (λ n → case (col n) 
            (LIST.case-cons (λ w0 → (w0 ∈ succ') + (Γ ⊢ A [ w0 ])) 
             (Inr D') Inl)
            Inr))
