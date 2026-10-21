# APEX 로드맵: Lean 전체를 향해

**방향 (확정): 증명/수학 중심, Lean 노선.** 소유권/빌림 검사(M5)는 이미 있는 부가 기능으로 동결하고
더 확장하지 않는다. 시스템 언어 쪽(네이티브 백엔드, Drop, 정제 타입)은 Lean 쪽이 갖춰진 뒤에 다시 본다.

목표는 Lean 4의 기능 전체다. 끝이 있는 목표가 아니므로 의존 순서대로 마일스톤을 쌓는다.
각 마일스톤은 테스트와 문서를 함께 커밋하고, 구현하지 못한 것은 문서에 "하지 않음"으로 남긴다.

## A. 커널 완성
- [x] A-1a 커널의 상호 귀납형 (`add_mutual`: 모티브/마이너 전체 공유, 재귀자별 ι-규칙; 테스트 `mutual_tree_forest_recursion_reduces`)
- [~] A-1b 표면 문법 `mutual { enum .. enum .. }`, `match`/`cases`/`induction`(다른 타입의 모티브는 상수 `PUnit`), 상호 구조적 재귀 `mutual { fn .. fn .. }`(타입마다 함수 하나, 첫 매개변수로 감소, 공유 재귀자로 정의), 일반 `injection`/`contradiction`(생성자 불일치). 중첩 귀납형(`List<Tree>` 필드)은 아직 (커널의 보조 타입 번역 필요)
- [x] A-2 구조 η (필드 타입이 앞 필드에 의존하지 않는 구조체; 의존 구조체와 단위형 η는 아직)
- [x] A-3 몫 `Quot` (mk/lift/ind/sound, lift 계산 규칙은 커널 whnf), 공리 `propext`/`Classical.choice`, `funext`는 Quot.sound에서 유도(공리 아님). 표면 문법 `forall(x: A) -> T` 추가
- [x] A-4 인덱스 족: 표면 문법 `enum Even(n: Nat): Prop { Zero: Even(0), Add2<k: Nat>(Even(k)): Even(k + 2) }` / `enum Vec<T>(n: Nat) { .. }`, `induction`/`cases`가 인덱스를 추상화(변수가 아닌 인덱스는 등식 `heq_i`로 일반화). `match`(B-2)는 아직
- [~] A-5 완료: 커널이 `nat_sub/nat_beq/nat_lt/nat_div/nat_rem`을 리터럴(u64)에서 직접 계산(`APEX_NO_ACCEL=1`로 끄고 정의 펼침과 격자 대조 테스트), 독립 검증기 크레이트 `apex-verify`(커널과 코드 공유 없음, `apex verify file.apex`; 귀납형·재귀자는 주어진 것으로 받고 타입만 검사, 곱셈수는 무시). 아직: 임의 정밀도(bignum), `String` 리터럴 가속

## B. 엘라보레이터
- [x] B-1a 구조적 재귀의 일반화: 커널이 `T.below`/`T.brecOn`을 생성(인덱스 없는 단순 귀납형), 엘라보레이터는 직접 필드 재귀가 안 되면 brecOn 모드로 재시도 (`fib(m)+fib(m+1)`, 3단계 깊이, 리스트 두 칸 건너뛰기). 한계: 인덱스/상호/중첩/선형 필드 타입, 고차 재귀 필드는 brecOn이 없음
- [x] B-1b 잘 정초된 재귀: `fn f(..) termination_by m decreasing_by { .. } { .. }` (생략하면 매개변수를 측도로 추정, 감소 증명은 기본 `omega`), `if` 조건이 가설로 보인다, `f.eq` 풀이 등식 자동 생성. 커널에 `Acc`/`WellFounded.fix`/`fix_eq`. 사전순(lexicographic) 측도와 상호 재귀는 아직
- [x] B-2 종속 패턴 매칭: 인덱스 족에 대한 `match`는 탭틱 엔진의 `cases`로 컴파일된다. 인덱스가 변수가 아니면 등식 `heq`로 일반화하고, `Nat` 인덱스 등식은 변수 제거(`Eq`의 `cases`로 커널이 의존 항을 옮긴다)나 `omega` 모순으로 푼다. 불가능한 생성자는 팔이 필요 없다(`vhead`). 재귀(`vmap`), 중첩 `match`(`vzip`) 지원. 한계: 인덱스 타입은 `Nat`만, 팔 안 패턴은 평평(중첩은 중첩 `match`로)
- [x] B-3 `namespace`/`open`/`section`/`variable` (`fn`·`theorem`만 접두사; `struct`/`enum`/`trait`은 이름공간 안에서도 전역 이름. `universe`는 아직: 우주는 암시적). 섹션 변수는 언급한 선언에 선행 인자로 붙는다 (재귀 호출에서는 직접 넘겨야 함)
- [~] B-4 `struct B extends A`(부모 필드 앞에 복사, 비제네릭이면 `toA()`), `#[derive(BEq, Show, Ord)]`(구조체·열거형, 제네릭 가능, 재귀 열거형은 도우미 함수 `T_derived_beq`로). `class` 출력 매개변수·기본 인스턴스는 아직
- [~] B-5 완료: `Coe` 강제 변환(한 단계), 타입 표기 `(e : T)`, 항 자리의 `by { .. }`, `universe u;`와 `Type(u)`/`Sort(max(u, v))`(함수·정리만; 열거형·구조체는 아직 우주 고정), `Int`(음수 `-e`, 리터럴 강제 변환, 법칙 전부 증명), `Option`/`Subtype`/`Sigma`(의존 필드가 있는 구조체), `exists(x: A) -> P`, trait의 `out` 매개변수. 아직: 암시 람다(암시성은 상수별 마스크라 타입에 없음), 기본 인스턴스

## C. 메타프로그래밍
- [x] C-1 사용자 정의 문법: `infixl|infixr|infix N "op" => f;`, `prefix N "op" => f;`(연산자는 렉서가 선언을 보고 토큰화, 우선순위는 Lean 숫자를 결합력으로 변환), `macro name(a, b) => 템플릿;`(구문 치환, 위생적이지 않음). 탭틱 블록 안에서도 동작. 구문 범주/`syntax`/`macro_rules` 패턴/`elab`은 아직(C-2)
- [ ] C-2 `MetaM`/`TacticM`, `elab`; 탭틱을 APEX 자신으로 재작성 (부트스트랩)

## D. 자동화
- [x] D-1 `omega` (Nat 선형 산술, 검증된 증명서 검사기; Int·`/`·`%`·정수 타이트닝은 아직)
- [x] D-2 `simp` 확장 (`at`, 조건부 재작성, `simp only`/`simp_arith`/`simp_all`; 합동 기반 재작성은 아직)
- [~] D-3 `ring`(`Nat` 가환 반환, 반사적 증명: 정규화기와 건전성 증명이 `prelude_ring.apex`) 완료. `linarith`는 `omega`의 별칭, `Int`/체/`nlinarith`는 아직
- [x] D-4 `conv`: `conv [at h] { lhs; arg 2; enter [1,2]; fun; rw/simp/unfold/.. }` (앞쪽 이동 명령 뒤 하위 항에서 `s = ?s'`를 증명). 이동 명령을 섞어 쓰는 것과 `ext`/`intro`는 아직
- [x] D-5 `auto`: 되돌리는 증명 탐색 (가설/`rfl`/`True`/모순/`intro`/`∧`·`∨` 분해와 선택/`simp`/`omega`/가설 분해/전방 추론/함의 적용; 깊이 6). `aesop`의 규칙 집합·우선순위·`simp_all` 통합은 없음

## E. 라이브러리
- [~] E-1 core 라이브러리: `Nat` 순서·산술 정리(`prelude_omega.apex`, ~700줄)와 `List` 보조정리(`prelude_core.apex`: append/map/len/sum/reverse/range/filter), 모두 증명됨. 이름을 언급할 때만 로드. `Int`/`Array`/`String`/`Option`/`HashMap`은 아직
- [ ] E-2 Mathlib 규모 수학

## F. 도구와 런타임
- [x] F-1 네이티브 백엔드: `apex compile f.apex -o out`이 지우기(erasure)된 IR 중 `main`이 닿는 것을 데이터로, 느긋한 환경 기계의 C 이식(`runtime.c`)과 함께 C로 내보내 `cc`로 빌드한다 (`tests/run/*.apex` 32개가 인터프리터와 같은 출력). 한계: 최적화하는 AOT가 아니라 같은 기계를 C로 옮긴 것, GC 없음(메모리를 해제하지 않음), `Nat`은 u128. Cranelift/LLVM 대신 C를 택함
- [x] F-2 패키지/모듈: `apex.toml`, `import a.b;`(의존성 먼저 로드, 순환 검출), `apex new/build/run/test` (원격 레지스트리·버전 해석은 없음)
- [x] F-3 REPL: `apex repl` (선언 누적, 식 평가, `:type NAME`). `apex lsp`는 진단(parse/elab 오류와 위치)만
- [x] F-4 문서 생성: `apex doc` (시그니처와 `///` 주석 → Markdown)
- [x] F-5 증분 컴파일: `apex build`는 소스+컴파일러 지문(`target/apex-build.stamp`)이 같으면 "up to date"로 건너뛰고, 번들 라이브러리의 증명은 디스크 캐시(`~/.cache/apex`)에서 가져온다. 파일 단위가 아니라 프로젝트 단위(환경이 파일들 사이에서 공유되므로)
