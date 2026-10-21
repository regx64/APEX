# APEX 엘라보레이터 (M3a–c, 기반 정리)

`crates/apex-elab`: 표면 AST를 커널 항으로 바꾼다. **신뢰하지 않는다.** 산출물은 메타변수를 모두 제거(zonk)한 뒤
깨끗한 `TypeChecker`가 `Env::add_def`/`add_inductive`로 다시 전부 검사한다.

## 메타변수와 단일화
- 커널 `Term::MVar`, `Level::MVar`는 엘라보레이션 중에만 존재한다. 메타변수가 없는 새 체커는 `MVar`를 거부한다.
- `TypeChecker::is_def_eq`가 Miller 패턴(`?m x1 .. xn`, xi는 서로 다른 지역변수)까지 대입하고 occurs check를 한다.
- 유니버스 레벨은 `Sort ?u` 단일화로 풀린다. 예: `Eq ?A ?a ?a`와 `Eq.{1} Nat ..`.
- 예상 타입으로 암시 인자를 먼저 풀어 보고, 실패하면 대입을 롤백(`snapshot`/`restore`)한다.

## 암시 인자
상수마다 "어느 Π 바인더가 암시인가" 마스크를 둔다. `fn`/`theorem`의 제네릭은 암시, 일반 매개변수는 명시.
enum/struct 생성자와 필드 프로젝션은 타입 매개변수가 암시. 호출 `f(a, b)`는 앞쪽 암시 인자를 메타변수로 채운다.

## 지원하는 구문 (M3a)
| 항목 | 상태 |
|---|---|
| `fn`, `theorem`(항 증명) | 됨 |
| `enum`(재귀 포함), `struct`(+프로젝션 `p.x`) | 됨. 인덱스 없는 단일 inductive |
| `let`, 블록, `if`/`else`(Bool.rec), `()`, 자연수 리터럴 | 됨 |
| `+ - * / % == < >` | 트레잇 `Add Sub Mul Div Rem BEq Ord`로 풀린다. `=`는 명제 동치 |
| `own x: T` | 곱셈수 1. 커널이 선형 사용을 검사 |
| 클로저 `|x, y: T| body` | 됨: 매개변수 타입은 기대 타입에서 가져오거나 주석 |
| 리스트 `[a, b]`, `for x in xs { .. }` (`do` 안), `range(n)` | 됨 (아래 참고) |
| `match` (중첩 패턴, `_`, 변수, 생성자, 자연수 리터럴, 완전성 검사) | 됨 |
| 구조적 재귀 `fn` | 됨 (아래 참고) |
| 트레잇, impl, 경계 `T: A + B`, 메서드 호출, 연산자 오버로딩 | 됨 (아래 참고) |
| 탭틱 증명 | M6 |
| 참조 `&T`, `&mut T`, `&x`, `*x` | 값 의미론: 타입에서는 `T`로 소거되고, 빌림 검사는 `apex-borrowck` (docs/OWNERSHIP.md) |
| `let mut`, `x = e`, `x += e`, `x.f = e`, `&mut` 인자 | 됨: 순수 항으로 바뀐다 (docs/OWNERSHIP.md) |
| 문자열, 음수, `- / == < >` | 미정 |

## 구현 메모
- 제네릭이 타입(Sort를 타입으로 갖는 변수)이면 곱셈수 0, 아니면 ω.
- recursor의 motive는 곱셈수 0(소거). `Eq`, `List`의 타입 매개변수도 0.
- `let` 변수는 불투명한 지역변수로 엘라보레이트하고 마지막에 `Let` 항으로 감싼다.
- `std`급 이름은 `prelude.apex`(표면 소스, 현재 `rfl`)와 커널 prelude(`Nat`, `Bool`, `Unit`, `Eq`, `List`)로 제공.

## match 컴파일
패턴 행렬을 결정 트리로 바꾼다. 첫 행에서 생성자 패턴이 있는 가장 왼쪽 열을 골라 그 열의 변수에 대해
`I.rec`을 만들고(생성자마다 minor premise), 행을 그 생성자로 특수화해 재귀한다. 변수/`_` 패턴 행은 모든
분기로 복제된다. 분기가 비면 `non-exhaustive patterns: missing `C`` 오류. 분기 안에서 스크루티니 변수는
생성자 적용으로 치환된다 (예: `n * fact(m)`의 `n`은 `succ m`).

## 구조적 재귀
본문이 자기 이름을 언급하면 매개변수를 하나씩 "감소하는 인자" 후보로 시도한다.
- 그 매개변수에 대한 최상위 `match`의 motive가 나머지 명시 매개변수를 일반화한다: `fun t => Π others, R[t]`.
  그래서 호출마다 다른 누산기나 다른 인자를 넘길 수 있다.
- 재귀 필드마다 귀납 가설 `ih : Π others, R[field]`이 생기고, 재귀 호출 `f(.., field, ..)`은 `ih(others..)`로 바뀐다.
- 인자가 그 `match`가 만든 필드가 아니면 `not structural` 오류.
- 커널에는 재귀가 없다: 결과 정의에는 `f` 자신이 나타나지 않고 recursor만 쓴다. 그래서 `fact(3) = 6`이 `rfl`로 증명된다.

한계: 직접 필드에 대한 호출만 허용 (`fib(n-2)`처럼 깊은 필드는 `below`/`brecOn`이 필요 → 후속).
상호 재귀 없음. 인덱스가 있는 inductive(`Vec`, `Eq`)의 `match` 없음. 선형(`own`) 값에 대한 `match`는
recursor의 주 전제 바인더가 ω이므로 곱셈수 오류가 난다. 다른 매개변수의 타입이 감소 인자에 의존하면 실패할 수 있다.

## 트레잇 (M3c)
딕셔너리 전달 방식이다. 트레잇은 구조체(클래스)로, impl은 그 값(정의)으로 바뀐다.
- `trait T<A> { fn m(&self, ..) -> R; }` → 단일 생성자 inductive `T (Self : Type) (A ..)`. 필드가 메서드 타입.
  메서드 `T.m`은 프로젝션이고 인스턴스를 **인스턴스 암시 인자**(`Bk::Inst`)로 받는다:
  `T.m : Π {Self} {A..} [inst : T Self A..], Π params, R`.
- `impl<G: B> T<A> for Ty { .. }` → 정의 `inst_T_n : Π G [dicts], T Ty A := T.mk Ty A (메서드 항들)`.
  메서드는 트레잇이 요구하는 타입과 정의적으로 같아야 하고, 빠지거나 남는 메서드는 오류.
- 경계 `T: Show + Default`는 `T`와 함께 사전(런타임 값) 매개변수를 추가한다. 함수 안에서는 그 사전이 지역 인스턴스.
- 호출 `f(x)`: 인스턴스 바인더는 메타변수가 되고 목록에 쌓였다가, 인자를 엘라보레이트한 뒤(타입이 정해진 뒤)
  `synth`가 푼다: 지역 인스턴스 → 선언된 impl(그 impl의 경계는 하위 목표로 재귀, 깊이 12).
- **일관성**: 두 impl의 머리가 단일화되면 선언 시점에 `overlaps` 오류 (`impl<T> Tag for T`는 모든 것과 겹침).
- **추론**: Rust처럼, impl로부터 타입을 *결정*하지 않는다. 타입이 끝까지 모르는 목표는 `cannot tell which implementation`.
  (impl이 하나뿐이어도 마찬가지다: 나중에 impl을 추가해도 기존 코드가 깨지지 않게.)
- 메서드 호출 `x.m(..)`: 타입 머리의 `Ty.m`(inherent impl 또는 구조체 프로젝션)을 먼저, 없으면 `m`을 가진 트레잇을 찾는다.
  `T.m(..)`처럼 대상이 타입이면 `Self := T`인 정적 호출 (Rust의 `T::m()`).
- `impl Ty { fn m(&self, ..) }`(트레잇 없음)은 정의 `Ty.m`이 된다. `Self`는 impl의 타입.
- 연산자: `a + b` → `Add.add(a, b)`, `a > b` → `Ord.lt(b, a)`. 프렐류드가 `Nat`, `String`, `Bool`에 대한 impl을 정의한다.
- **인라인(devirtualization)**: 인스턴스가 닫힌 상수이면 `T.m Ty inst`를 `whnf`로 메서드 본문으로 바꾼다. 정적으로
  알려진 호출은 사전 비용이 없다 (`acc + n`이 `Nat.add acc n`이 됨).
- 인터프리터는 프렐류드의 `nat_sub`/`nat_beq`/`nat_lt`를 네이티브로 대체한다 (증명은 정의를 본다).

### 메서드 제네릭, 기본 메서드, 미완성 impl
- **메서드 제네릭** `fn fold<B>(&self, init: B, step: Nat -> B -> B) -> B`: 필드 타입이 `Π (B : Type), ..`이 되어
  한 우주 위(`Sort 2`)에 산다. 그런 메서드가 있는 트레잇만 클래스가 `Sort 2`이고, 호출 지점에서 `B`는 암시 인자다.
- **기본 메서드**: 트레잇의 본문 있는 메서드. impl이 생략하면 **그 impl 안에서** 기본 본문을 다시 엘라보레이트한다
  (`Self`가 impl의 타입이 됨). 트레잇 선언 시점에는 본문을 검사하지 않는다.
- **형제 메서드 호출**: 커널에 재귀가 없으므로 impl은 자기 자신 전체를 쓸 수 없다. 대신 impl을 짓는 동안
  *임시 사전*(`Trait.mk Ty .. 지은 메서드들 .. 자리표시자`)을 인스턴스로 제공하고, 인라인이 호출을 지은 메서드 본문으로 바꾼다.
  자리표시자(아직 안 지은 메서드)가 결과에 남으면 `is used before it is defined` 오류. 메서드는 선언 순서와 무관하게
  의존성 순서로 지어진다 (필요한 형제를 아직 못 지었으면 나중에 다시 시도). 자기 자신이나 상호 재귀는 오류.

### 리스트와 `for`
- `[a, b, c]`는 커널 `List`의 `cons`/`nil`로 바뀐다. `List<T>`는 커널 prelude의 `List`.
- `for x in xs { body }`는 `do` 안에서 `for_each(xs, |x| do { body })`. `xs`는 `List`여야 한다 (일반 `Iterator`는 연관 타입이 필요해서 아직).
- 라이브러리(prelude.apex): `range`, `list_len/append/map/filter/foldl/sum/reverse`, `for_each`, `Show for List<T>`.

### 클로저
`|x, y| body`. 기대 타입이 함수 타입이면 매개변수 타입을 거기서 가져온다 (`list_map(xs, |x| x + 1)`),
아니면 `|x: Nat|`처럼 주석이 필요하다. 변수를 캡처한다 (커널 λ).

### 나눗셈
`nat_div`는 피제수를 연료로 쓰는 반복 뺄셈 (`a + 1`번이면 충분). `a / 0 = 0`, `a % 0 = a` (Lean과 같음).
인터프리터가 `nat_div`/`nat_rem`/`nat_sub`/`nat_beq`/`nat_lt`를 네이티브로 대체한다 (증명은 정의를 본다).

### 이름 가리기 (shadowing)
사용자 함수/정리는 프렐류드의 이름을 가릴 수 있다. 가린 정의는 커널에 `name'user`로 등록되고 표면 이름이 그쪽을 가리킨다.
프렐류드 안의 호출은 영향받지 않는다. 같은 이름을 사용자 코드에서 두 번 정의하면 오류. (타입/트레잇은 가릴 수 없다.)

### 구조적 재귀 보완
중첩 `match`가 필드 변수를 생성자 적용으로 바꿔도(`_ =>` 분기에서 `rest`가 `cons a b`가 됨) 재귀 호출 `f(rest)`를 알아본다.

### 한계
- 연관 타입, 상위 트레잇(`trait A: B`), 고차 종류(`Self: Type -> Type`, 즉 `Functor`)가 없다.
- 타입 선언의 경계 (`struct W<T: Show>`)가 없다.
- 인스턴스/메서드가 자기 자신을 재귀적으로 쓸 수 없다. 헬퍼 함수를 만들어 impl이 위임하게 쓴다.
- `T::method` 대신 `T.method(..)`이고, `<T as Trait>::m` 문법이 없다.
- `Iterator`와 일반 모나드 `do`는 아직이다 (`IO` 전용).
- **깊은 필드 재귀**(`fib(n)`이 `fib(n-1) + fib(n-2)`를 부르는 꼴)는 안 된다. 직접 필드(`succ m`의 `m`)만 귀납 가설이 된다.
  일반 해법은 `below`/`brecOn`인데, 중첩 `match`의 모티브가 귀납 가설에 의존하는 *의존 일반화*가 필요하다.
  당분간 누산기(`fib_iter(n, a, b)`)나 쌍을 돌려주는 헬퍼로 쓴다.
- 클로저 매개변수의 `own`/다중도, 클로저 안에서의 재귀, 제네릭 클로저는 없다.

## 다음
M5 (소유권, 빌림 검사).


## 구조적 재귀의 두 모드 (M6 이후)

1. **직접 필드 재귀**: 매개변수에 대한 최상위 `match`를 `I.rec`로 컴파일하고 재귀 필드마다 귀납 가설(ih)을 둔다. 빠르고 항이 작다.
2. **course-of-values (brecOn)**: 1이 실패하면 `I.brecOn x (fun x b others => 본문) others`로 다시 시도한다.
   `b : I.below motive x`는 모든 하위 항의 결과를 묶은 `PProd` 튜플이다. `match`가 `x`를 쪼갤 때마다 모티브가 `b`도 일반화하고,
   각 분기에서 `b`의 `PProd` 성분(`fst`=재귀 결과, `snd`=그 필드의 below)을 꺼내 재귀 필드에 등록한다.
   그래서 `fib(m) + fib(m+1)`처럼 임의 깊이의 하위 항을 부를 수 있고, 항은 여전히 `rfl`/`decide`로 계산된다.
   `T.below`/`T.brecOn`은 커널이 귀납형마다 만드는 평범한 정의라서 신뢰 대상이 아니다.

## 잘 정초된 재귀

`fn f(..) -> R termination_by m(..) decreasing_by { 탭틱 } { 본문 }` (docs/ROADMAP B-1b). 구조적 재귀가 안 되고 `termination_by`가 없으면
각 매개변수를 측도로 시도한다. 정의는 `Nat`과 `lt` 위의 `WellFounded.fix`:

    f params := fix lt_wf (fun n ih params hm => 본문) (m params) params rfl      (hm : m params = n)

본문의 재귀 호출 `f(b)`는 `ih (m b) pf b rfl`가 된다. `pf : lt (m b) n`은 `decreasing_by`(기본 `omega`)가 그 호출 지점의 문맥에서 증명한다.
문맥에는 `hm`, 그리고 `if c {..} else {..}`의 조건 `c = true/false`가 들어 있다 (`if`가 `Bool.rec (fun b => c = b → R) .. c rfl`로 컴파일된다).
`omega`는 `nat_lt`/`nat_beq`의 `= true/false` 사실을 `lt`/`=`/`≠`로 바꿔 쓴다. 커널은 `fix`를 계산하지 못하므로(접근성 증명이 불투명) 본문을 한 번 더
재귀 호출을 일반 호출로 둔 채 엘라보레이션해서 풀이 등식 `f.eq : f params = 본문`을 `WellFounded.fix_eq`와 `congr_arg`로 증명한다.
인터프리터는 `fix`를 일반 고정점으로 실행한다.


## 상호 귀납형과 상호 재귀 (A-1b)

`mutual { enum Tree<T> { Node(T, Forest<T>) } enum Forest<T> { Nil, Cons(Tree<T>, Forest<T>) } }`는 커널의 `MutualDecl` 하나로 들어간다
(모티브는 타입마다 하나, 마이너는 가족 전체 생성자 순서, `IndInfo.family`가 가족을 기록). `match`/`cases`/`induction`은 현재 타입의 모티브만 실제로 쓰고
다른 타입의 모티브는 상수 `PUnit`, 마이너는 `PUnit.unit`이다.

`mutual { fn size_tree<T>(t: Tree<T>) -> Nat {..} fn size_forest<T>(f: Forest<T>) -> Nat {..} }`는 타입마다 함수 하나, 첫 매개변수로 감소하는 구조적 상호 재귀다.
각 함수의 `match`에서 자기 타입의 마이너를 뽑아(`Cx::mutual_minors`) 모으고, 모든 함수를 공유 재귀자 `Tree.rec`(모티브: 타입별 `fun t => Π others, R`)로 정의한다.
형제 호출 `size_forest(f)`는 그 필드의 귀납 가설이 된다. 한계: 타입당 함수 하나, 첫 매개변수만 감소, 중첩 귀납형(`List<Tree>` 필드)은 커널의 보조 타입 번역이 필요해 아직.

## 라이브러리 증명 캐시

번들 라이브러리(`prelude_omega/ring/int/classical/core`)는 정리가 많아 처음 로드할 때 수 초가 걸린다. 한 번 엘라보레이트하면 정리의 증명 항을
`~/.cache/apex`(또는 `APEX_CACHE_DIR`)에 `apex-kernel::ser`의 DAG 형식으로 저장하고, 다음 실행은 **정리의 명제만** 엘라보레이트하고 증명은 캐시에서 가져온다
(`Env::add_def_trusted`: 타입은 검사, 값은 검사하지 않음). 키는 라이브러리 소스와 실행 파일(크기·수정시각)의 해시다. 캐시는 신뢰 데이터라서
`APEX_NO_CACHE=1`로 끌 수 있고, 독립 검증기(`apex verify`)는 처음부터 다시 검사한다.

## 강제 변환, 타입 표기, `by` 항

`impl Coe<B> for A`가 있으면 `A`가 필요한 곳에 `B`를 줄 수 있다 (`coerce`가 `Coe.coe`를 끼운다; 한 단계만). `Nat` 리터럴이 `Int`가 되는 것도 이것이다.
`(e : T)`는 타입 표기, `-e`는 `Neg.neg(e)`. `by { .. }`는 항 자리에서도 쓸 수 있다: 기대 타입의 미지수가 풀린 뒤에 증명한다 (`PendingBy`).

## 중첩 귀납형 (A-1b)

필드 타입이 `J args`(기존 귀납형 `J`에 가족 자신을 담은 인자)이면 커널(`nested.rs`)이 보조 타입 `Fam._nestedK`를 가족에 추가한다. 보조 타입의 생성자는 `J`의 것을
`args`로 치환해 복사한 것이고 (J의 재귀 필드는 보조 타입 자신을 가리킨다; 더 깊은 중첩은 반복 발견). 확장된 가족의 재귀자를 평소처럼 만든 뒤,
보조 타입/생성자를 `J args`/`J.c args`로 되돌려 `Fam.rec`(동기 N+보조 개수의 모티브)와 `Fam._nestedK.rec`(대상은 `J args`, 규칙은 `J`의 생성자)로 등록하고,
번역된 재귀자를 다시 타입 검사한다. `IndInfo.nested`가 보조 항목(재귀자 이름, `J`, 인자 틀, 생성자)을 기록한다. `match`/`cases`/`induction`은 보조 모티브를
상수 `PUnit`으로 채우고, `mutual { fn f(r: Rose) fn g(ks: List<Rose>) }`의 `g`는 `List.rec`이 아니라 보조 재귀자로 정의된다 (`AuxView`).
