# APEX 커널 (M2)

신뢰 영역: `crates/apex-kernel`. 이 크레이트만 정리의 정당성을 보장한다.

## 항 (`term.rs`)
`BVar | FVar | Sort | Const | App | Lam | Pi | Let`. bound 변수는 de Bruijn 인덱스, 바인더를 지나갈 때는
고유 id를 가진 `FVar`를 쓰는 locally nameless 방식(`instantiate` / `abstract_fvars`).
모든 바인더(`Lam`/`Pi`/`Let`)가 곱셈수 `Mult = 0 | 1 | ω`를 가진다.

## 유니버스 (`level.rs`)
`Zero | Succ | Max | IMax | Param`. 정규형 `max(base+offset)`으로 비교한다. `leq`/`equiv`는 보수적이다
(참이면 항상 참, 거짓이면 모를 수 있음). 선언은 유니버스 매개변수 `lparams`를 가질 수 있다.

## 타입체커 (`tc.rs`)
- `infer`: 일반적인 CIC 규칙. Π는 `imax`, Prop은 impredicative.
- 환원: β, ζ, ι(recursor), δ(정의 펼치기). `whnf_core`(δ 제외)와 `whnf`.
- 정의적 동치: 구조적 비교 + 게으른 δ(나중에 정의된 상수를 먼저 펼침) + η + 증명 무관성(Prop).
- 곱셈수 검사 (`check_mults`): 런타임에 관련된 위치(타입과 소거된 인자 제외)에서 변수 사용량을 세어
  `0`은 0회, `1`은 정확히 1회를 요구한다. 함수 적용에서 인자의 사용량은 함수 Π 바인더 곱셈수만큼 곱해진다.

## Inductive 타입 (`inductive.rs`)
단일(비상호) inductive, 인덱스 지원. 검사: 생성자 반환 타입, strict positivity, 필드 유니버스,
인덱스에 자기 자신 등장 금지. 생성: recursor `I.rec` 타입과 ι 규칙.
Prop의 inductive는 subsingleton(생성자 0개 또는 필드가 모두 Prop/인덱스인 1개)일 때만 large elimination.
실패한 선언은 환경에서 롤백된다.

## 검증된 것 (`tests/kernel.rs`)
`Nat.add_zero`(rfl), `congrArg`(Eq.rec), `Nat.zero_add`(귀납법), 리스트 길이 계산, η, 증명 무관성,
`0 + n = n`을 rfl로 증명하려는 시도 거부, 타입 오류/positivity/유니버스 초과/미선언 유니버스 거부,
선형 변수의 복제·폐기·ω 인자 전달 거부, 선형 생성자 필드 허용, 소거된 변수의 런타임 사용 거부.

## 메타변수 (M3a에서 추가)
`MVar`(항, 레벨)와 대입 테이블은 `TypeChecker` 안에만 있다. 새 체커는 `MVar`를 거부하므로 최종 검사는 영향받지 않는다. 자세한 내용은 ELAB.md.

## 알려진 한계 (다음 단계에서 해결)
- recursor의 바인더는 모두 ω. 선형 필드를 가진 타입의 선형 `match`는 엘라보레이터(M3)/MIR(M5)에서 검사한다.
- 상호/중첩 inductive, 구조체 프로젝션/η, 자연수 리터럴, K-규칙 없음.
- 정의적 동치에 캐시가 없어 큰 증명에서 느릴 수 있다. 환원은 재귀 구현이라 깊은 항에서 스택을 쓴다.
- 독립 재검증기와 proptest는 아직 없다 (PLAN의 위험 3).
