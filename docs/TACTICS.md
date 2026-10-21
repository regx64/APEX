# APEX 탭틱 증명 (M6)

**상태: 구현됨** (`crates/apex-elab/src/elab/tactic.rs`, 파서는 `apex-syntax`의 `parse_tactics`).
테스트: `tests/ui/check/ok/tactics_*.apex`, `tests/ui/check/err/tac_*.apex`, 그리고 프렐루드의 정리 라이브러리
(`prelude.apex` 끝부분 — 전부 탭틱으로 증명되어 있다).

## 1. 원리: 탭틱은 증명 항을 만드는 프로그램

`theorem t(..): P := by { ... }` 는 `P`를 목표(goal)로 시작한다. 목표는 **메타변수** 하나와 자기 지역 문맥
(가설 목록)이다. 탭틱은 첫 목표를 항으로 풀되, 그 항이 새 목표를 포함할 수 있다.

- `intro`류는 첫 목표를 `fun x => ?새목표`로 푼다 (Lam 해).
- `apply f`는 `f ?1 ?2`로 풀고 결정되지 않은 `?i`가 새 목표가 된다.
- 끝나면 모든 해를 한 항으로 합치고, **커널이 다시 검사한다.**

그래서 탭틱은 신뢰 대상이 아니다. 탭틱이 틀리면 오류가 날 뿐 거짓 정리가 통과하지 않는다 (엘라보레이터와 같은 원칙).

## 2. 문법

```apex
theorem add_comm(a: Nat, b: Nat): a + b = b + a := by {
    induction b with {
        zero => { simp },
        succ(k, ih) => { simp [ih] },
    }
}
```

탭틱은 `;`나 공백으로 구분한다. `{ ... }`는 첫 목표를 **반드시 닫는** 블록이다.
`#[simp]`를 정리 앞에 붙이면 `simp`의 기본 규칙이 된다 (`#[simp] theorem zero_add(n: Nat): 0 + n = n := ...`).
명제는 `a = b`, `And<P, Q>`, `Or<P, Q>`, `Not<P>`, `True`, `False`, `P -> Q`로 쓴다.

| 탭틱 | 하는 일 |
|---|---|
| `intro x y` | `P -> Q`, `Not<P>`의 가정을 가설로 (이름 생략 시 `h`) |
| `exact e` | 항 `e`로 목표를 닫는다 |
| `apply f` | `f`의 결론을 목표에 단일화, 남은 인자가 새 목표 |
| `rfl` | `a = b`를 정의적 동치로 닫는다 |
| `assumption` | 목표와 같은 가설로 닫는다 |
| `constructor` | 생성자가 하나인 귀납 명제 (`And`, `True`, `Eq`)의 생성자를 적용 |
| `left` / `right` | `Or.inl` / `Or.inr` |
| `exfalso` | 목표를 `False`로 바꾼다 |
| `contradiction` | `False` 가설, 또는 `P`와 `P -> False` 가설 쌍 |
| `symm` | `a = b`를 `b = a`로 |
| `show T` | 목표를 정의적으로 같은 `T`로 바꾼다 |
| `have h: T := e` / `:= by { .. }` | 보조 사실을 가설로 |
| `rw [h, <- g]` | 등식으로 다시 쓴다 (`<-`는 오른쪽에서 왼쪽). 끝나면 `rfl`을 시도한다 |
| `simp [h, f]` | 재작성을 반복 (`#[simp]` 정리 + 주어진 가설/정의). 끝나면 `rfl`/`assumption` |
| `unfold f` | 정의 `f`를 펼친다 (뒤에 `rfl` 시도) |
| `induction x with { c(a, ih) => { .. }, .. }` | `x`에 대한 귀납 (재귀 인자마다 `ih`) |
| `cases x with { c(a) => { .. }, .. }` | 경우 나누기 (`And`, `Or`, `False`, `Nat`, 사용자 `enum` …) |
| `decide` | 닫힌 명제(`=`, `And`, `Or`, `True`)를 계산으로 증명, 거짓이면 오류 |

`with { .. }`를 생략하면 새 목표들이 순서대로 남는다 (자동 이름 `x1`, `ih`), 각각 `{ .. }` 블록으로 닫는다.
오류는 실패한 탭틱의 위치와 **그 시점의 목표**(`case`, 가설, `⊢ 목표`)를 보여 준다.

## 3. 재작성 (rw / simp) 의 구현

규칙 `∀ args, lhs = rhs`를 인자마다 메타변수로 열고, 목표에서 `lhs`와 **1차 구조 매칭**되는 첫 부분 항 `s`를 찾는다
(계산으로 맞추지 않는다: 그렇지 않으면 `n * succ(m)`이 `0 * a`와 맞아 버린다). 그런 다음
`s`의 모든 출현을 모티브 `fun x => 목표[x/s]`로 추상화하고
`Eq.subst motive (rhs = lhs) ?새목표`로 푼다. `simp`는 이 한 걸음을 규칙이 더 맞지 않을 때까지 반복한다
(500걸음 상한; 조건부 규칙(미결정 가설 인자)은 건너뛴다).

## 4. 프렐루드의 논리와 정리 라이브러리

커널 프렐루드: `True`, `False`, `And`, `Or`, `Not`, `Eq.subst/symm/trans`, `congr_arg`, `And.left/right`, `False.elim`.
`prelude.apex`: `add_zero/add_succ/zero_add/succ_add/add_comm/add_assoc`, `mul_zero/mul_succ/zero_mul/succ_mul/mul_one/one_mul/mul_comm`.
사용자 정리가 같은 이름이면 이름 가리기로 사용자 것이 우선한다.

## 5. 하지 않는 것 (솔직하게)

- **`omega`**: 파서는 알지만 "not implemented"로 거부한다. 증명 항을 만드는 선형 산술 결정 절차(또는 반사 증명)가 필요하다.
- `rw ... at h`, `simp at h`, `simp`의 조건부 재작성, 합동(congruence) 기반 재작성 (지금은 모티브 방식).
- 인덱스가 있는 귀납 족(`Eq`, 벡터)에 대한 `induction`/`cases`, 그리고 목표가 의존하는 가설이 있을 때의 자동 일반화
  (`generalizing`). 후자는 "hypothesis depends on" 오류로 거부한다.
- `Exists`, `Iff`, 순서 관계 `<`/`≤`의 명제 버전 (`<`는 `Bool`을 돌려준다). `decide`는 `Not`을 모른다.
- 상호 재귀/깊은 필드 재귀 함수에 대한 방정식 보조정리 자동 생성 (재귀 함수는 `induction` 뒤 `rfl`/`simp [f]`의 계산으로).
- 탭틱 매크로, `repeat`/`try`/`first`/`<;>` 조합자, `sorry`.
