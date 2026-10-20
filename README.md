# APEX
Advanced Proof & Expression Language — Lean식 의존 타입·증명과 Rust식 소유권을 결합한 언어.

- 계획: [docs/PLAN.md](docs/PLAN.md), 명세 초안: [docs/SPEC.md](docs/SPEC.md)
- 현재: M3a 완료 (렉서, 파서, 진단, 커널, 엘라보레이터 1차). `cargo run -p apex-driver -- check tests/ui/check/ok/data.apex`. 설계: [docs/KERNEL.md](docs/KERNEL.md). `cargo run -p apex-driver -- parse tests/ui/ok/items.apex`

설계 문서: [KERNEL](docs/KERNEL.md), [ELAB](docs/ELAB.md)
