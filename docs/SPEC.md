# APEX 언어 명세 (초안)

## 렉싱
- 주석: `//` 줄, `/* */` 중첩 가능
- 정수: `123`, `1_000`; 문자열 이스케이프: `\n \t \" \\`
- 키워드: fn struct enum trait impl theorem let match by own mut unsafe for if else `_`
- 라이프타임: `'a`
- 기호: `( ) { } [ ] , ; : := -> => & + - * / = == . < > |`

## 타입과 곱셈수 (QTT)
인자는 곱셈수 `0 | 1 | ω`를 가진다.
- `0`: 컴파일 타임에만 존재, 소거된다 (타입, 증명)
- `1` (`own`): 정확히 한 번 사용(이동)
- `ω`: 자유롭게 복사 (`Copy` 타입 기본값)

## 소유권
- 이동 후 사용은 오류. `Drop`은 스코프 종료 시 삽입.
- `&T` 공유 빌림, `&mut T` 배타적 빌림(공유 XOR 가변). 검사는 MIR 단계(NLL).
- 라이프타임은 Rust의 생략 규칙으로 추론하고, 모호할 때만 `'a`를 명시한다. 라이프타임은 MIR 분석용 region 변수로, 커널 타입에는 들어가지 않고 소거된다.
- 타입에 나타난 값의 사용은 곱셈수 0이므로 이동으로 간주하지 않는다.

## 구문 (M1 파서 기준)
- 선언: `fn struct enum trait impl theorem`. 파라미터는 `name: Type`, 선형 인자는 `own name: Type`, 메서드는 `&self` / `&mut self`.
- 제네릭은 `<T, n: Nat, 'a>`. 타입 위치(`:`, `->` 뒤)에서 `<`는 제네릭 인자, 값 위치에서는 비교 연산자.
- `=`는 명제적 동치, `==`는 불리언 동치. `let x := e;`로 바인딩.
- 증명: `:= by { 탭틱... }` 또는 `:= 항`. 탭틱은 docs/TACTICS.md.

## 예시
```apex
theorem add_comm(a: Nat, b: Nat): a + b = b + a := by {
    induction b with {
        zero => { simp },
        succ(k, ih) => { simp [ih] },
    }
}
```
