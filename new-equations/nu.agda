
open import Agda.Builtin.Nat
open import Data.Fin hiding (fold)
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality


data Type (n : Nat) : Set where
  `alpha : (k : Fin n) → Type n
  _`→_ : (σ : Type n) → (τ : Type n) → Type n
  _`×_ : (σ : Type n) → (τ : Type n) → Type n
  `𝟙 : Type n
  `list : (σ : Type n) → Type n

infixr 20 _`→_
infixl 30 _`×_

data Context (T : Set) : Set where
  ε : Context T
  _,,_ : Context T → T → Context T

data In-context {n : Nat} : Context (Type n) → Type n → Set where
  in-Z : ∀ {Γ σ} → In-context (Γ ,, σ) σ
  in-S : ∀ {Γ τ σ} → In-context Γ σ → In-context (Γ ,, τ) σ
  
data Tm {n : Nat} : Context (Type n) → Type n → Set where
  tm-var : ∀ {Γ σ} → In-context Γ σ → Tm Γ σ
  tm-app : ∀ {Γ σ τ} → Tm Γ (σ `→ τ) → Tm Γ σ → Tm Γ τ 
  tm-lam : ∀ {Γ σ τ} → Tm (Γ ,, σ) τ → Tm Γ (σ `→ τ)

  tm-pair : ∀ {Γ σ τ} → Tm Γ σ → Tm Γ τ → Tm Γ (σ `× τ)
  tm-proj1 : ∀ {Γ σ τ} → Tm Γ (σ `× τ) → Tm Γ σ
  tm-proj2 : ∀ {Γ σ τ} → Tm Γ (σ `× τ) → Tm Γ τ

  tm-unit : ∀ {Γ} → Tm Γ `𝟙

  tm-empty : ∀ {Γ σ} → Tm Γ (`list σ)
  tm-cons : ∀ {Γ σ} → Tm Γ σ → Tm Γ (`list σ) → Tm Γ (`list σ)
  tm-fold : ∀ {Γ σ τ} → Tm Γ (σ `→ τ `→ τ) → Tm Γ τ → Tm Γ (`list σ) → Tm Γ τ
  tm-map : ∀ {Γ σ τ} → Tm Γ (σ `→ τ) → Tm Γ (`list σ) → Tm Γ (`list τ)
  tm-append : ∀ {Γ σ} → Tm Γ (`list σ) → Tm Γ (`list σ) → Tm Γ (`list σ)

module inclusion {n : Nat} where

  data _⊆_ : Context (Type n) → Context (Type n) → Set where
    base : ε ⊆ ε
    both : ∀ {Γ Δ σ} → Γ ⊆ Δ → (Γ ,, σ) ⊆ (Δ ,, σ)
    step : ∀ {Γ Δ σ} → Γ ⊆ Δ → Γ ⊆ (Δ ,, σ)

  inc-id : {Γ : Context (Type n)} → Γ ⊆ Γ
  inc-id {Γ = ε} = base
  inc-id {Γ = Γ ,, x} = both (inc-id)

  inc-trans : ∀ {Γ Δ Δ'} → Γ ⊆ Δ → Δ ⊆ Δ' → Γ ⊆ Δ'
  inc-trans inc1 base = inc1
  inc-trans (both inc1) (both inc2) = both (inc-trans inc1 inc2)
  inc-trans (step inc1) (both inc2) = step (inc-trans inc1 inc2)
  inc-trans inc1 (step inc2) = step (inc-trans inc1 inc2)
  
open inclusion

interleaved mutual

  data Ne {n : Nat} : Context (Type n) → Type n → Set
  data Nf {n : Nat} : Context (Type n) → Type n → Set

  data Ne where
    ne-var : ∀ {Γ σ} → In-context Γ σ → Ne Γ σ
    ne-app : ∀ {Γ σ τ} → Ne Γ (σ `→ τ) → Nf Γ σ → Ne Γ τ
    ne-proj1 : ∀ {Γ σ τ} → Ne Γ (σ `× τ) → Ne Γ σ
    ne-proj2 : ∀ {Γ σ τ} → Ne Γ (σ `× τ) → Ne Γ τ
    ne-fold : ∀ {Γ σ τ} → Nf Γ (σ `→ τ `→ τ) → Nf Γ τ → Ne Γ (`list σ) → Ne Γ τ

  data Nf where
    nf-ne : ∀ {Γ k} → Ne Γ (`alpha k) → Nf Γ (`alpha k)
    nf-lam : ∀ {Γ σ τ} → Nf (Γ ,, σ) τ → Nf Γ (σ `→ τ)
    nf-pair : ∀ {Γ σ τ} → Nf Γ σ → Nf Γ τ → Nf Γ (σ `× τ)
    nf-unit : ∀ {Γ} → Nf Γ `𝟙
    nf-empty : ∀ {Γ σ} → Nf Γ (`list σ)
    nf-cons : ∀ {Γ σ} → Nf Γ σ → Nf Γ (`list σ) → Nf Γ (`list σ)
    nf-mapappend : ∀ {Γ τ σ} → Nf Γ (τ `→ σ) → Ne Γ (`list τ) → Nf Γ (`list σ) → Nf Γ (`list σ)

data 𝑳 {n : Nat} (Γ : Context (Type n)) (σ : Type n) (Ms : (Context (Type n) → Set)) : Set where
  l-empty : 𝑳 Γ σ Ms
  l-cons : Ms Γ → 𝑳 Γ σ Ms → 𝑳 Γ σ Ms
  l-mapappend : ∀ {τ} → (F : ∀ {Δ} → (inc : Γ ⊆ Δ) → Ne Δ τ → Ms Δ)
                      → (n : Ne Γ (`list τ)) → 𝑳 Γ σ Ms
                      → 𝑳 Γ σ Ms

𝑴 : {n : Nat} → (Γ : Context (Type n)) → Type n → Set
𝑴 Γ `𝟙 = ⊤
𝑴 Γ (`alpha k) = Ne Γ (`alpha k)
𝑴 Γ (σ `× τ) = 𝑴 Γ σ × 𝑴 Γ τ
𝑴 Γ (σ `→ τ) = (Δ : _) → (inc : Γ ⊆ Δ) → 𝑴 Δ σ → 𝑴 Δ τ
𝑴 Γ (`list σ) = 𝑳 Γ σ (λ · → 𝑴 · σ)

module weakening {n : Nat}  where

  private
    lemma : {Γ Δ : Context (Type n)} {σ : Type n} (inc : (Γ ,, σ) ⊆ Δ) → In-context Δ σ
    lemma (both inc) = in-Z
    lemma (step inc) = in-S (lemma inc)

    lemma2 : {Γ Δ : Context (Type n)} {σ : Type n} (inc : (Γ ,, σ) ⊆ Δ) → Σ[ Δ' ∈ Context (Type n) ] (Γ ⊆ Δ' × Δ' ⊆ Δ)
    lemma2 {Γ = Γ} {Δ = Δ ,, σ} {σ = .σ} (both inc) = Δ , (inc , step inc-id)
    lemma2 {Γ = Γ} {Δ = Δ ,, τ} {σ = σ} (step inc) = Δ' , evi1 , step evi2
      where
        Δ' : Context (Type n)
        Δ' = proj₁ (lemma2 inc)
        evi1 : Γ ⊆ Δ'
        evi1 = proj₁ (proj₂ (lemma2 inc))
        evi2 : Δ' ⊆ Δ
        evi2 = proj₂ (proj₂ (lemma2 inc))

  wk-in-context : {Γ Δ : Context (Type n)} {σ : Type n} (inc : Γ ⊆ Δ) → In-context Γ σ → In-context Δ σ
  wk-in-context inc in-Z = lemma inc
  wk-in-context {Γ = Γ ,, τ} {Δ = (Δ ,, τ)} {σ = σ} (both inc) (in-S inctx) = in-S (wk-in-context inc inctx)
  wk-in-context {Γ = Γ ,, τ} {Δ = (Δ ,, σ')} {σ = σ} (step inc) (in-S inctx) = in-S (wk-in-context inc (in-S inctx))

  interleaved mutual

    wk-ne : {Γ Δ : Context (Type n)} {σ : Type n} (inc : Γ ⊆ Δ) → Ne Γ σ → Ne Δ σ
    wk-nf : {Γ Δ : Context (Type n)} {σ : Type n} (inc : Γ ⊆ Δ) → Nf Γ σ → Nf Δ σ

    wk-ne {Γ = Γ} {Δ = Δ} {σ = σ} inc (ne-var x) = ne-var inctx
        where
        inctx : In-context Δ σ
        inctx = wk-in-context inc x
    wk-ne {Γ = Γ} {Δ = Δ} {σ = σ} inc (ne-app n x) = ne-app (wk-ne inc n) (wk-nf inc x)
    wk-ne {Γ = Γ} {Δ = Δ} {σ = σ} inc (ne-proj1 n) = ne-proj1 (wk-ne inc n)
    wk-ne {Γ = Γ} {Δ = Δ} {σ = σ} inc (ne-proj2 n) = ne-proj2 (wk-ne inc n)
    wk-ne {Γ = Γ} {Δ = Δ} {σ = σ} inc (ne-fold xf xe n) = ne-fold (wk-nf inc xf) (wk-nf inc xe) (wk-ne inc n)

    wk-nf {Γ} {Δ} {.(`alpha _)} inc (nf-ne x) = nf-ne (wk-ne inc x)
    wk-nf {Γ} {Δ} {(σ `→ τ)} inc (nf-lam nf) = nf-lam (wk-nf inc2 nf)
      where
        inc2 : (Γ ,, σ) ⊆ (Δ ,, σ)
        inc2 = both inc
    wk-nf {Γ} {Δ} {.(_ `× _)} inc (nf-pair nf-fir nf-sec) = nf-pair (wk-nf inc nf-fir) (wk-nf inc nf-sec)
    wk-nf {Γ} {Δ} {.`𝟙} inc nf-unit = nf-unit
    wk-nf {Γ} {Δ} {.(`list _)} inc nf-empty = nf-empty
    wk-nf {Γ} {Δ} {.(`list _)} inc (nf-cons nf-head nf-tail) = nf-cons (wk-nf inc nf-head) (wk-nf inc nf-tail)
    wk-nf {Γ} {Δ} {.(`list _)} inc (nf-mapappend f n ys) = nf-mapappend (wk-nf inc f) (wk-ne inc n) (wk-nf inc ys)

  interleaved mutual

    wk-L : {Γ Δ : Context (Type n)} {σ : Type n} {Ms : Context (Type n) → Set}
           {convert : {Δ : Context (Type n)} → Ms Δ → 𝑴 Δ σ}
           {convert-back : {Δ : Context (Type n)} → 𝑴 Δ σ → Ms Δ}
         → (inc : Γ ⊆ Δ) → 𝑳 Γ σ Ms → 𝑳 Δ σ Ms
    wk-M : {Γ Δ : Context (Type n)} {σ : Type n} (inc : Γ ⊆ Δ) → 𝑴 Γ σ → 𝑴 Δ σ

    wk-L inc l-empty = l-empty
    wk-L {Ms = Ms} {convert = convert} {convert-back = cb} inc (l-cons x l) = l-cons x' l'
      where
        x' = cb (wk-M inc (convert x))
        l' = wk-L {convert = convert} {convert-back = cb} inc l
    wk-L {Γ} {Δ} {Ms = Ms} {convert = cv} {convert-back = cb} inc (l-mapappend F ne l) = l-mapappend (λ {Δ'} inc' nx → F (inc-trans inc inc') nx) ne' l'
      where
        ne' = wk-ne inc ne
        l' = wk-L {convert = cv} {convert-back = cb} inc l

    wk-M {Γ} {Δ} {`alpha k} inc v = wk-ne inc v
    wk-M {Γ} {Δ} {σ `→ τ} inc v = λ Δ' inc' x → v Δ' (inc-trans inc inc') x
    wk-M {Γ} {Δ} {σ `× τ} inc (x , y) = wk-M inc x , wk-M inc y
    wk-M {Γ} {Δ} {`𝟙} inc v = tt
    wk-M {Γ} {Δ} {`list σ} inc v = wk-L {Ms = λ · → 𝑴 · σ} {convert = λ u → u} {convert-back = λ u → u} inc v

open weakening

module reify-and-reflect {n : Nat} where

  interleaved mutual

    reify : {Γ : Context (Type n)} {σ : Type n} → 𝑴 Γ σ → Nf Γ σ
    reify-list : {Γ : Context (Type n)} {σ : Type n} {Ms : Context (Type n) → Set}
               → {convert : {Δ : Context (Type n)} → Ms Δ → 𝑴 Δ σ}
               → 𝑳 Γ σ Ms → Nf Γ (`list σ)
    reify-nefun : {Γ : Context (Type n)} {σ τ : Type n}
                → (F : ∀ {Δ} → Γ ⊆ Δ → Ne Δ σ → 𝑴 Δ τ) → Nf Γ (σ `→ τ)
    reflect : {Γ : Context (Type n)} {σ : Type n} → Ne Γ σ → 𝑴 Γ σ

    reify-nefun {Γ} {σ} {τ} F = nf-lam (reify (F inc x))
      where
        Δ : Context (Type n)
        Δ = Γ ,, σ
        inc : Γ ⊆ Δ
        inc = step inc-id
        x : Ne (Γ ,, σ) σ
        x = ne-var in-Z

    reify {σ = `alpha k} v = nf-ne v
    reify {Γ} {σ `→ τ} v = nf-lam (reify (v Δ inc (reflect x)))
      where
        Δ : Context (Type n)
        Δ = Γ ,, σ
        inc : Γ ⊆ Δ
        inc = step inc-id
        x : Ne (Γ ,, σ) σ
        x = ne-var in-Z

    reify {σ = σ `× τ} (fst , snd) = nf-pair (reify fst) (reify snd)
    reify {σ = `𝟙} v = nf-unit
    reify {σ = `list σ} v = reify-list {Ms = λ · → 𝑴 · σ} {convert = λ {u} v → v} v

    reify-list l-empty = nf-empty
    reify-list {Γ = Γ} {convert = convert} (l-cons x v) = nf-cons (reify (convert x)) (reify-list {convert = convert} v)
    reify-list {Γ = Γ} {σ = σ} {convert = convert} (l-mapappend {τ = τ} F nl v) = nf-mapappend nf-F nl nf-YS
      where
        Δ : Context (Type n)
        Δ = Γ ,, τ
        inc : Γ ⊆ Δ
        inc = step inc-id
        nf-F : Nf Γ (τ `→ σ)
        x : Ne Δ τ
        x = ne-var in-Z
        nf-F = nf-lam (reify (convert (F {Δ} inc x)))
        nf-YS = reify-list {convert = convert} v

    reflect {σ = `alpha k} n = n
    reflect {σ = σ `→ σ₁} n = λ Δ inc x → reflect (ne-app (wk-ne inc n) (reify x))
    reflect {σ = σ `× σ₁} n = (reflect (ne-proj1 n)) , (reflect (ne-proj2 n))
    reflect {σ = `𝟙} n = tt
    reflect {Γ = Γ} {σ = `list σ} n = l-mapappend F-id n l-empty
      where
        F-id : {Δ : Context (Type _)} → Γ ⊆ Δ → Ne Δ σ → 𝑴 Δ σ
        F-id inc ne = reflect ne

open reify-and-reflect

data SemEnv {n : Nat} (Δ : Context (Type n)) : (Γ : Context (Type n)) → Set where
  se-empty : SemEnv Δ ε
  se-more : ∀ {Γ σ} → SemEnv Δ Γ → 𝑴 Δ σ → SemEnv Δ (Γ ,, σ)

sem-env-lookup : {n : Nat} {Γ Δ : Context (Type n)} {σ : Type n} → SemEnv Δ Γ → In-context Γ σ → 𝑴 Δ σ
sem-env-lookup {Γ = .(_ ,, σ)} {Δ = Δ} {σ = σ} (se-more E x) in-Z = x
sem-env-lookup {Γ = .(_ ,, _)} {Δ = Δ} {σ = σ} (se-more E x) (in-S inctx) = sem-env-lookup E inctx

sem-env-wk : {n : Nat} {Γ Δ Δ' : Context (Type n)} → (inc : Δ ⊆ Δ') → SemEnv Δ Γ → SemEnv Δ' Γ
sem-env-wk inc se-empty = se-empty
sem-env-wk inc (se-more E x) = se-more (sem-env-wk inc E) (wk-M inc x)


module evaluation {n : Nat} where

  interleaved mutual

    compose : {Γ : Context (Type n)} {σ τ τ' : Type n} →
              (f : (Δ' : Context (Type n)) → Γ ⊆ Δ' → 𝑴 Δ' τ → 𝑴 Δ' τ') →
              (g : {Δ : Context (Type n)} → Γ ⊆ Δ → Ne Δ σ → 𝑴 Δ τ) →
              ((Δ'' : Context (Type n)) → Γ ⊆ Δ'' → Ne Δ'' σ → 𝑴 Δ'' τ')
    compose {Γ} {σ} {τ} {τ'} f g Δ'' inc ne = f Δ'' inc (g inc ne)

    eval : {Γ Δ : Context (Type n)} {σ : Type n} → Tm Γ σ → SemEnv Δ Γ → 𝑴 Δ σ
    do-fold : {Γ : Context (Type n)} {σ τ : Type n} → 𝑴 Γ (σ `→ τ `→ τ) → 𝑴 Γ τ → 𝑴 Γ (`list σ) → 𝑴 Γ τ
    do-map : {Γ : Context (Type n)} {σ τ : Type n} → 𝑴 Γ (σ `→ τ) → 𝑴 Γ (`list σ) → 𝑴 Γ (`list τ)
    do-append : {Γ : Context (Type n)} {σ : Type n} → 𝑴 Γ (`list σ) → 𝑴 Γ (`list σ) → 𝑴 Γ (`list σ)

    do-fold {Γ} {σ} {τ} mf me l-empty = me
    do-fold {Γ} {σ} {τ} mf me (l-cons x ml) = mf Γ inc-id x Γ inc-id (do-fold mf me ml)
    do-fold {Γ} {σ} {τ} mf me (l-mapappend F nl ml) = reflect (ne-fold (reify-nefun (λ {Δ} → compose mf F Δ)) (reify (do-fold mf me ml)) nl)

    do-map {Γ} {σ} {τ} mf l-empty = l-empty
    do-map {Γ} {σ} {τ} mf (l-cons x ml) = l-cons (mf Γ inc-id x) (do-map mf ml)
    do-map {Γ} {σ} {τ} mf (l-mapappend G ne ml) = l-mapappend (λ {Δ} → compose mf G Δ) ne (do-map mf ml)

    do-append {Γ} {σ} l-empty ml2 = ml2
    do-append {Γ} {σ} (l-cons x ml1) ml2 = l-cons x (do-append ml1 ml2)
    do-append {Γ} {σ} (l-mapappend F ne ml1) ml2 = l-mapappend F ne (do-append ml1 ml2)

    eval {Γ} {Δ} {σ} (tm-var inctx) E = sem-env-lookup E inctx
    eval {Γ} {Δ} {σ} (tm-app t1 t2) E = f Δ inc-id x
      where
        f : (Δ' : Context (Type n)) (inc : Δ ⊆ Δ') (x : 𝑴 Δ' _) → 𝑴 Δ' σ
        f = eval t1 E
        x : 𝑴 Δ _
        x = eval t2 E

    eval {Γ} {Δ} {(σ `→ τ)} (tm-lam t) E Δ' inc x = eval t E'
      where
        wE : SemEnv Δ' Γ
        wE = sem-env-wk inc E
        E' : SemEnv Δ' (Γ ,, σ)
        E' = se-more wE x
    eval {Γ} {Δ} {.(_ `× _)} (tm-pair t1 t2) E = eval t1 E , eval t2 E
    eval {Γ} {Δ} {σ} (tm-proj1 t) E = proj₁ (eval t E)
    eval {Γ} {Δ} {σ} (tm-proj2 t) E = proj₂ (eval t E)
    eval {Γ} {Δ} {.`𝟙} tm-unit E = tt
    eval {Γ} {Δ} {`list σ} tm-empty E = l-empty
    eval {Γ} {Δ} {`list σ} (tm-cons t-head t-tail) E = l-cons (eval t-head E) (eval t-tail E)
    eval {Γ} {Δ} {σ} (tm-fold tf te tl) E = do-fold (eval tf E) (eval te E) (eval tl E)
    eval {Γ} {Δ} {(`list σ)} (tm-map tf tl) E = do-map (eval tf E) (eval tl E)
    eval {Γ} {Δ} {σ} (tm-append t1 t2) E = do-append (eval t1 E) (eval t2 E)

open evaluation

module normalization {n : Nat} where

  diag-sem-env : (Γ : Context (Type n)) → SemEnv Γ Γ
  diag-sem-env ε = se-empty
  diag-sem-env (Γ ,, x) = se-more (sem-env-wk (step inc-id) (diag-sem-env Γ)) (reflect (ne-var in-Z))

  norm : {Γ : Context (Type n)} {σ : Type n} → Tm Γ σ → Nf Γ σ
  norm {Γ = Γ} t = reify (eval t (diag-sem-env Γ))

open normalization

module example {n : Nat} {k : Fin n} {σ : Type n} where

  ex : Tm ε (`list (`𝟙 `× `alpha k) `→ `list (`𝟙 `× `alpha k))
  ex = tm-lam (tm-var in-Z)

  norm_ex : norm ex ≡
    nf-lam (nf-mapappend (nf-lam (nf-pair nf-unit (nf-ne (ne-proj2 (ne-var in-Z))))) (ne-var in-Z) nf-empty)
  norm_ex = refl
