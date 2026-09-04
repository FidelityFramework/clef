# Certification Lab Strategy

> Labs are the gatekeepers of certification. Make them fluent in your tooling and they become your distribution channel.

## Overview

Clef and Atelier provide certification labs (Common Criteria CCTLs, safety-critical assessment bodies) with evaluation capabilities that dramatically reduce the cost and time of product certification. The strategy: provide the tooling free for evaluation work, license commercially when labs build bridge tooling on the platform.

## The Lab Opportunity

Certification labs perform the gatekeeping function for safety-critical and security-critical products. Every product seeking DO-178C, IEC 61508, ISO 26262, IEC 62304, or Common Criteria certification must pass through a lab evaluation. Labs evaluate dozens of products per year and have direct influence over technology recommendations to product developers.

Today, lab evaluation work is largely manual:
- Tracing security functional requirements to code locations via spreadsheets
- Reading source and assembly side-by-side to verify generated code
- Running static analysis tools that produce findings without traceability
- Writing evaluation technical reports (ETRs) by hand
- Performing data flow analysis with limited tooling and high false-positive rates

Clef's graph-native compilation and Atelier's Pipeline Inspector transform this work. A lab evaluating a Clef-built product can navigate from a security requirement directly to the PSG nodes that implement it, through every compilation phase down to assembly, with proof obligations verified along the way.

## Licensing Model

### Free: Evaluation Use

Labs receive Atelier and the Clef toolchain at no cost for the purpose of evaluating products built in Clef. This creates:

- Lab fluency in Clef's compilation model and traceability capabilities
- Firsthand experience with the quality of evidence the toolchain produces
- Organic recommendations to product developers seeking certification
- A distribution channel into every company pursuing safety-critical or security-critical certification

### Licensed: Bridge Tooling and Custom Integrations

When labs build their own tooling on top of Clef's compilation pipeline, that is a commercial license. Bridge tooling includes:

- Custom evidence extractors that pull PSG traceability data into evaluation management systems
- Automated report generators that produce ETR sections from compilation artifacts
- Integration with lab workflow tools (test management, requirement tracing, document generation)
- Custom analysis tools that consume PSG, coeffect, and proof obligation data

## Competitive Reference: Ferrocene

Ferrocene (Ferrous Systems) provides a qualified Rust compiler toolchain with:
- Individual tier at €25/seat/month (compiler only, qualification docs excluded)
- Enterprise tier at custom pricing (qualification signatures, assessor reports, target enablement, certification assistance)
- Certifications: ISO 26262 ASIL D, IEC 61508 SIL 4, IEC 62304 Class C
- No DO-178C certification achieved

Key structural differences:

| | Ferrocene | Clef |
|---|---|---|
| Business model | Charge developers for qualified compiler | Give labs the evaluation tool free; charge for bridge tooling |
| Tool qualification | Qualify monolithic rustc + LLVM (expensive, per-platform) | Qualify nanopasses independently (modular, incremental) |
| Target enablement | Expensive: re-qualify entire compiler for each new platform | Modular: qualify only the new Alex substrate backend |
| Traceability | Developer's responsibility despite compiler opacity | PSG produces traceability artifacts as a compilation byproduct |
| Formal verification | External tools, bolt-on | Proof-carrying compilation, integrated |
| Lab relationship | No direct lab engagement model | Labs are first-class partners and distribution channel |

Ferrocene validates the market: companies pay for qualified toolchains. Clef's architecture solves what Ferrocene's approach cannot (full traceability, formal verification, modular qualification) and the lab-first go-to-market creates a distribution channel Ferrocene lacks.

## The Flywheel

1. Labs receive Atelier free and become fluent in the tooling
2. Labs evaluate products built in Clef and see the traceability advantage
3. Labs recommend Clef to product developers seeking certification
4. More Clef-built products enter evaluation, increasing lab investment
5. Labs build bridge tooling (licensed commercially) to increase their efficiency
6. Labs with custom Clef tooling prefer evaluating Clef products
7. Stronger lab preference drives stronger developer recommendations

Each cycle reinforces the previous one. Labs that invest in bridge tooling have a financial incentive to recommend Clef to product developers, because their evaluation workflow is optimized for it.

## CC-Specific Value

### EAL 5+ Enablement

Most products stop at EAL 4 because semiformal and formal verification methods required at EAL 5-7 are prohibitively expensive to produce manually. Proof-carrying compilation makes higher EAL levels tractable: the compiler generates the formal evidence that labs need to assess.

### Security Domain Mapping

Common Criteria evaluation decomposes the Target of Evaluation (TOE) into security domains with controlled interfaces. Clef's actor model with BAREWire message contracts maps directly to this decomposition. The security architecture IS the program architecture. Labs can inspect actor boundaries as security domain boundaries, and BAREWire contracts as the controlled interfaces between domains.

### Covert Channel Analysis

CC evaluations at higher EALs require covert channel analysis, proving that information cannot leak through timing or resource usage side channels. Flow loss analysis directly supports this: serialization points (where the compiler introduced sequencing in the control-flow lowering) are exactly the locations where timing-based covert channels could exist. The flow loss metric quantifies this surface.

### Automated Evidence

The PSG with source ranges through every nanopass phase, combined with proof obligations and coeffect annotations, constitutes evaluation evidence that would normally require weeks of manual analysis to produce. Atelier's Pipeline Inspector renders this evidence navigably. Bridge tooling can extract it programmatically for ETR generation.

## Safety-Critical Value

### Modular Tool Qualification

DO-178C (via DO-330), IEC 61508, and ISO 26262 all require tool qualification. Qualifying a monolithic compiler is expensive and must be repeated per-platform. Clef's nanopass architecture allows:

- Shared pipeline (CCS, Baker, nanopasses, PSG elaboration) qualifies once
- Each Alex substrate backend qualifies independently
- Adding a new target means qualifying only that backend against the already-qualified shared pipeline
- Cost of target enablement is a fraction of monolithic compiler qualification

### PSG as Certification Artifact

The PSG with full source-to-object traceability is itself a certification artifact. For DO-178C Level A, the auditor needs to trace every assembly instruction back to a source requirement. The PSG provides this mapping as a natural byproduct of compilation. Atelier renders it. Bridge tooling can export it in whatever format the certification authority requires.

## Revenue Streams

| Stream | Description | Timing |
|---|---|---|
| Lab bridge tooling licenses | Labs building custom evaluation tools on Clef pipeline | After lab adoption |
| Developer toolchain licenses | Per-seat qualified toolchain (Ferrocene-style pricing) | After tool qualification |
| Target enablement | Qualifying new Alex backends for customer-specific hardware | On demand |
| Certification artifacts | Qualification signatures, assessor reports | After tool qualification |
| Training | Lab evaluator training, developer safety-critical training | Ongoing |
| Certification consulting | Program-level certification assistance | Ongoing |

## Target Relationships

### US
- NIAP-approved CCTLs (Common Criteria evaluation)
- DO-178C Designated Engineering Representatives (avionics)
- Defense supply chain (increasing interest in formal methods, CMMC compliance)

### Europe
- TÜV organizations (Germany, already evaluates Ferrocene)
- BSI-approved labs (UK, Germany)
- ANSSI-approved labs (France)
- Automotive assessment services (ISO 26262)

### Industrial
- IEC 61508 assessment bodies (oil and gas, power, manufacturing)
- IEC 62304 notified bodies (medical devices)
- Nuclear safety assessment (IEC 61513)
