# APEX 실행 (M4, M4b)

`crates/apex-eval`: 검사를 통과한 커널 선언을 소거하고 실행한다. `apex run file.apex`는 파일을 검사한 뒤
`fn main()`의 값을 평가해 출력한다.

## 소거 (`erase.rs`)
커널 항 → 타입 없는 람다 IR (`Var`, `Lam`, `App`, `Global`, `Nat`, `Let`, `Erased`).
- 타입(Sort를 타입으로 갖는 항)과 증명(Prop에 사는 항)은 `Erased`.
- 곱셈수 0 바인더의 인자도 `Erased`. 단, **인자 자리는 남긴다**: 생성자와 recursor의 논리적 인자 위치가 유지된다.
- 소거 여부는 커널 타입체커로 각 부분항을 추론해 결정한다 (항 크기에 대해 이차 비용, M7에서 개선).

## 평가 (`eval.rs`)
call-by-need 환경 기계. 지연 평가가 필요한 이유: 정의가 recursor로 컴파일되므로 귀납 가설(ih)은
분기가 쓸 때만 계산돼야 한다 (`pred(100000)`이 O(1)).
- `Nat`은 기계 정수(u128). `Nat.add`/`Nat.mul`은 내장 연산, 오버플로는 오류 (조용히 감기지 않는다).
- recursor는 커널이 만든 ι 규칙(`RecRule.rhs`)을 소거해 그대로 실행한다. 별도 의미론이 없으므로
  커널의 계산과 실행 결과가 어긋나기 어렵다.
- Prop의 subsingleton recursor(`Eq.rec`)는 주 전제가 소거돼 있어도 유일한 규칙으로 실행한다.
- 큰 스택(1 GiB) 스레드에서 실행한다.

## 커널 변경: Nat 리터럴
`Term::Lit(u64)`: `Lit(0) ≡ Nat.zero`, `Lit(n+1) ≡ Nat.succ (Lit n)`. recursor의 주 전제로 쓰이면 생성자로 펼쳐지고,
`Nat.add`/`Nat.mul`이 두 리터럴에 적용되면 바로 계산된다. 덕분에 `100000` 같은 수가 O(1)이다.

## 성능 (릴리스 빌드, 참고)
10만 단계 재귀 `sum_to`가 약 0.35초. 한 단계에 recursor 규칙 적용과 thunk 할당이 여러 번 일어난다.
recursor 패턴을 직접 재귀/루프로 되돌리는 최적화와 네이티브 코드는 M7.

## 문자열과 IO (M4b)
- `String`은 커널 공리 타입이고 `Term::Str`가 리터럴이다. 커널은 문자열을 계산하지 않는다 (구조적 동치만).
- `IO α`도 커널에서는 **불투명한 공리 타입**이다: `IO`, `IO.pure`, `IO.bind`, `IO.print`.
  그래서 커널은 순수하게 유지되고, 부수효과는 타입으로만 드러난다 (`IO` 없이는 출력할 수 없다).
- 런타임에서 IO 값은 액션(`Pure` / `Bind` / `Print`)이고, `run_io`가 명시적 continuation 스택으로 실행한다.
  그래서 5만 번 도는 `do` 루프도 Rust 스택을 쓰지 않는다.
- 표면 문법: `do { let x <- act; stmt; let y := e; tail }`.
  `let x <- e; rest` → `IO.bind e (fun x => rest)`, `e; rest` → `IO.bind e (fun _ => rest)`,
  마지막 식이 없으면 `pure(())`. `<-`는 `do` 밖에서 오류.
- 내장: `print(s)`, `println(s)`(prelude.apex에 표면 언어로 정의), `pure(x)`, `String.append`, `Nat.toString`.
- `fn main() -> IO<Unit>`이면 실행하고 출력을 돌려주며, 그 외의 `main`은 값을 출력한다.

## 한계
- 출력은 프로그램이 끝난 뒤 한꺼번에 나온다 (버퍼). 입력(`stdin`), 파일, 예외가 없다.
- `do`는 `IO`에만 동작한다. 일반 모나드는 트레잇(M3c) 이후.
- `let mut`과 변수 갱신, `for`/`while` 루프가 없다 (재귀로 쓴다).
- 문자열 연산은 `append`/`toString`뿐이고 `++`, 보간, 문자는 없다.
- 값 표시는 구조체 생성자 `S.mk`를 `S(..)`로, 그 외는 생성자 이름으로 보여 준다.
- 소거는 타입체커에 의존하므로 신뢰 영역은 아니지만, 소거 오류는 실행 결과를 틀리게 만들 수 있다.
