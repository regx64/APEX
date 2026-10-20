# APEX 엘라보레이터 (M3a)

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
| `+`, `*`, `=` | Nat 전용으로 고정 (트레잇 전까지) |
| `own x: T` | 곱셈수 1. 커널이 선형 사용을 검사 |
| `match`, 재귀 함수, 트레잇/impl, 메서드 호출 | M3b |
| 탭틱 증명 | M6 |
| 참조 `&T` | M5 (빌림 검사기와 함께) |
| 문자열, 음수, `- / == < >` | 미정 |

## 구현 메모
- 제네릭이 타입(Sort를 타입으로 갖는 변수)이면 곱셈수 0, 아니면 ω.
- recursor의 motive는 곱셈수 0(소거). `Eq`, `List`의 타입 매개변수도 0.
- `let` 변수는 불투명한 지역변수로 엘라보레이트하고 마지막에 `Let` 항으로 감싼다.
- `std`급 이름은 `prelude.apex`(표면 소스, 현재 `rfl`)와 커널 prelude(`Nat`, `Bool`, `Unit`, `Eq`, `List`)로 제공.

## 다음 (M3b)
`match` → `casesOn`/`rec` 컴파일, 구조적 재귀, 트레잇(인스턴스 인자), 메서드 호출, 숫자/연산자 오버로딩.
