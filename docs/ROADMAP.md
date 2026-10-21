# APEX 로드맵: Lean 전체를 향해

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
- [ ] B-1 잘 정초된 재귀 + `termination_by`/`decreasing_by`
- [ ] B-2 종속 패턴 매칭 (motive 일반화, 인덱스 족 `match`)
- [ ] B-3 `namespace`/`open`/`section`/`variable`/`universe`
- [ ] B-4 `structure` 상속, `class` 완전판(출력 매개변수, 기본 인스턴스), `deriving`
- [ ] B-5 강제 변환, 암시 람다, 서브타입/`Σ`/`∃` 표기

## C. 메타프로그래밍
- [ ] C-1 확장 가능한 문법 (`syntax`/`macro`/`notation`)
- [ ] C-2 `MetaM`/`TacticM`, `elab`; 탭틱을 APEX 자신으로 재작성 (부트스트랩)

## D. 자동화
- [ ] D-1 `omega`  D-2 `simp` 완전판(`at`, 조건부, 합동)  D-3 `ring`/`linarith`  D-4 `conv`  D-5 `aesop`류

## E. 라이브러리
- [ ] E-1 core (Nat/Int/List/Array/String/Option/HashMap)  E-2 Mathlib 규모 수학

## F. 도구와 런타임
- [ ] F-1 네이티브 백엔드(M7)  F-2 패키지 매니저  F-3 LSP/REPL  F-4 문서 생성  F-5 증분 컴파일
