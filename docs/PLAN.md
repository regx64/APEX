# APEX 구현 계획

APEX: Lean 수준의 의존 타입·증명 + Rust식 소유권/빌림/트레잇을 갖춘 언어. 구현 언어는 Rust.

## 결정 사항
- 이론: CIC 계열 커널 + QTT 곱셈수(0 소거 / 1 소유 / ω 복사)
- 빌림: 커널 밖, MIR 수준 NLL식 borrow checker. **모델 확정: Rust식 (공유 XOR 가변) + 라이프타임 생략 규칙, 필요 시에만 명시 `'a`** (Hylo식은 참조 반환/구조체 저장 제약이 커서 제외. 이후 Polonius로 개선 가능)
- 메모리: 소유권 + Drop, RC는 라이브러리(Rc/Arc)
- 증명(theorem/tactic)은 1급
- 백엔드: 트리 인터프리터 → Cranelift

## 크레이트
apex-span, apex-syntax, apex-kernel, apex-elab, apex-tactic, apex-mir, apex-borrowck, apex-codegen, apex-driver, apex-lsp, std/

## 마일스톤
| | 내용 | 완료 기준 |
|---|---|---|
| M0 | 명세, workspace, CI, 렉서 | `apex lex`가 동작, CI 통과 |
| M1 | 파서, 진단, fmt 기초 | 샘플이 AST로 파싱, 에러에 위치 표시 |
| M2 | 커널 (항, 유니버스, inductive, 정의적 동치, 곱셈수 검사) | `Nat.add_zero` 검증 |
| M3 | 엘라보레이터 (메타변수, 단일화, 암시 인자, 트레잇, match, 종료성) | `Vec`/`Option`/제네릭 타입체크 |
| M4 | 소거, 클로저 변환, 단형화, 인터프리터 | fib, 리스트, `main` 실행 (첫 사용 가능 버전) |
| M5 | 이동/Drop, MIR, 빌림 검사 | use-after-move, 이중 `&mut` 거부 |
| M6 | 탭틱 (intro/exact/apply/rw/induction/cases/simp/omega/decide) | 기초 정리 증명 |
| M7 | Cranelift 백엔드, FFI, unsafe | 네이티브 실행 |
| M8 | 패키지 매니저, LSP, REPL, 표준 라이브러리 | `apex build/run/test` |

## 위험
1. 의존 타입과 소유권의 상호작용 → 타입에 쓰이는 값은 곱셈수 0으로 규정
2. 엘라보레이터 복잡도 → 점진 확장
3. 커널 건전성 → 최소 커널 + 독립 검증기 + proptest
4. 범위 폭주 → M4까지를 먼저 완성

## 진행 상황
- M0, M1 완료. M2 커널 완료 (docs/KERNEL.md). M3a/M3b-1 완료: 엘라보레이터, match, 구조적 재귀 (docs/ELAB.md). M4 완료: 소거 + 지연 인터프리터, `apex run` (docs/EVAL.md). M4b 완료: String, IO, do 표기법, Hello World. M3c 완료: 트레잇, impl, 경계, 메서드 호출, 연산자 오버로딩. 기반 정리 완료: 클로저, 리스트, for, 나눗셈, 메서드 제네릭, 기본 메서드, 이름 가리기. M5 완료: 값 의미론의 `&mut`, 변이, 빌림 검사기 (docs/OWNERSHIP.md). 다음: M6 (탭틱) 또는 M7 (네이티브)
- M1 한계: 에러 복구 없음(첫 오류에서 중단), `apex fmt` 미구현
