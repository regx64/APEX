# APEX 로드맵: Lean 전체를 향해

**방향 (확정): 증명/수학 중심, Lean 노선.** 소유권/빌림 검사(M5)는 이미 있는 부가 기능으로 동결하고
더 확장하지 않는다. 시스템 언어 쪽(네이티브 백엔드, Drop, 정제 타입)은 Lean 쪽이 갖춰진 뒤에 다시 본다.

목표는 Lean 4의 기능 전체다. 끝이 있는 목표가 아니므로 의존 순서대로 마일스톤을 쌓는다.
각 마일스톤은 테스트와 문서를 함께 커밋하고, 구현하지 못한 것은 문서에 "하지 않음"으로 남긴다.

## A. 커널 완성
- [x] A-1a 커널의 상호 귀납형 (`add_mutual`: 모티브/마이너 전체 공유, 재귀자별 ι-규칙; 테스트 `mutual_tree_forest_recursion_reduces`)
- [ ] A-1b 표면 문법 `mutual { .. }`, 엘라보레이터/`match`/탭틱 지원, 중첩 귀납형 (`List<Tree>` 필드)
- [ ] A-2 구조 η, 단위형 η
- [ ] A-3 몫 `Quot` (mk/lift/ind/sound), 공리 `propext`, `Classical.choice`
- [ ] A-4 인덱스 족 전체 (`induction`/`cases`가 인덱스를 다루도록)
- [ ] A-5 `Nat`/`Int`/`String` 리터럴 가속(GMP급), 독립 검증기

## B. 엘라보레이터
- [x] B-1a 구조적 재귀의 일반화: 커널이 `T.below`/`T.brecOn`을 생성(인덱스 없는 단순 귀납형), 엘라보레이터는 직접 필드 재귀가 안 되면 brecOn 모드로 재시도 (`fib(m)+fib(m+1)`, 3단계 깊이, 리스트 두 칸 건너뛰기). 한계: 인덱스/상호/중첩/선형 필드 타입, 고차 재귀 필드는 brecOn이 없음
- [ ] B-1b 잘 정초된 재귀 + `termination_by`/`decreasing_by` (`Acc`, `WellFounded.fix`; `omega` 필요)
- [ ] B-2 종속 패턴 매칭 (motive 일반화, 인덱스 족 `match`)
- [ ] B-3 `namespace`/`open`/`section`/`variable`/`universe`
- [ ] B-4 `structure` 상속, `class` 완전판(출력 매개변수, 기본 인스턴스), `deriving`
- [ ] B-5 강제 변환, 암시 람다, 서브타입/`Σ`/`∃` 표기

## C. 메타프로그래밍
- [ ] C-1 확장 가능한 문법 (`syntax`/`macro`/`notation`)
- [ ] C-2 `MetaM`/`TacticM`, `elab`; 탭틱을 APEX 자신으로 재작성 (부트스트랩)

## D. 자동화
- [x] D-1 `omega` (Nat 선형 산술, 검증된 증명서 검사기; Int·`/`·`%`·정수 타이트닝은 아직)  D-2 `simp` 완전판(`at`, 조건부, 합동)  D-3 `ring`/`linarith`  D-4 `conv`  D-5 `aesop`류

## E. 라이브러리
- [ ] E-1 core (Nat/Int/List/Array/String/Option/HashMap)  E-2 Mathlib 규모 수학

## F. 도구와 런타임
- [ ] F-1 네이티브 백엔드(M7)  F-2 패키지 매니저  F-3 LSP/REPL  F-4 문서 생성  F-5 증분 컴파일
