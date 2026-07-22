# MatrixConcentration 机械层面健全性验证

> **GitHub 发布范围：**此检出版本仅包含验证脚本和 Markdown 结果报告。
> 原始日志、生成的 TSV/JSON/文本证据、整理输入、临时运行状态以及同级的
> `TranslationReport` 档案保留在本地。报告中的这些路径是来源记录，在此
> 精简版本中不要求可解析。脚本用于审阅；完整复跑仍需要未上传的输入，
> 因而此检出版本不是完整证据包。

完整的本地验证档案是 **MatrixConcentration 库机械层面健全性验证（本轮为修正后的重新认证）**
所对应的永久、可复现证据包；此 GitHub 目录发布其中的脚本和 Markdown 报告层。
它面向希望亲自核验 Lean 库、而非仅仅相信总结性结论的
维护者及持怀疑态度的第三方。本次重新认证于 2026 年 7 月 19–20 日完成，使用
Lean 4.31.0、Lake 5.0.0，以及通过哈希固定版本的 Mathlib 4.31 依赖项。

## 修正处置与迭代日志

下面的实时索引记录当前的重新认证结果。两个不可变快照保留了先前状态：
[修正前](README.pre-correction.md)和
[重新认证前](README.pre-recertification.md)。

| 轮次 | 日期 | 工作与结果 |
|---|---|---|
| 基线 | 2026 年 7 月 17–18 日 | 最初仅作记录的 V1–V9 检查报告了 1 个 MAJOR、4 个 MINOR 和 10 个 INFO 发现项，并将 5 个高于 INFO 级别的项目移交修正。 |
| 第 1 轮 | 2026 年 7 月 19 日 | 验证将两个项目判定为 CONFIRMED 并完成修复（V9-F1、V8-F1），将两个项目判定为不构成健全性缺陷、状态为 REJECTED（V6-F1、V6-F2），并修订了一个项目（V8-F2）。在全新的机器环境中完整重跑后全部通过，并在不改变任何定理签名的情况下达到修正不动点。 |
| 重新认证 | 2026 年 7 月 19–20 日 | 此前获接受的记录加入了 V10，使其环境清单与 V4 对齐，并以空队列完成了 368 项人工类型哈希义务。该记录中的 recovery-v6 构建及后续耗时/作业数据仅保留为历史证据；对于当前已修正的源码快照，它们已被新数据取代。 |
| 最终修正 | 2026 年 7 月 20 日 | 本轮修正删除了两个夸大书中公式 (6.1.6) 形式化覆盖范围的声明，同时保留有界的对称结果、带损失的中心化结果及其 `_aux` 辅助项，将其作为仅提供支持、不构成对应关系的基础设施。针对源码摘要 `38ffff…c89` 和验证输入摘要 `119519…6cf`，绑定源码的 recovery-v7、全新聚合检查、独立 V6/V7/V10 链以及最终生命周期/报告关卡均已通过。 |

## 总体健全性声明

在信任 Lean 4.31 内核和通过哈希固定的 Mathlib 依赖这一前提下，修正后的 15 文件
源码快照通过了隔离的 recovery-v7 构建、全新聚合检查以及独立 V6/V7/V10 检查。
每个被测项目声明至多使用 `propext`、`Classical.choice` 和 `Quot.sound`；唯一从未
实例化的类公理接口，是 V10-F1 中明确披露、未发布的 NC-Khintchine/bootstrap
辅助项，它们并非作为已确立结果呈现。唯一明确声明的书籍形式化覆盖例外是 UP-007 /
公式 (6.1.6)，本项目并未声称存在其已登记的 Lean 对应项。就这一精确的“书籍到 Lean”
意义而言，除公式 (6.1.6) 外，本项目的形式化是完整的。不动点证据链完整且经过独立认证：
最终生命周期检查器报告 `problems=0`、`result=PASS`、最终声明清单 14/14 PASS，且
写入锁和最终化保护均不存在。证书保持有效的前提是这两者始终不存在。

## 术语表

- **`sorry` / `sorryAx`：** `sorry` 是 Lean 的证明占位符；编译后对它的使用会留下可检测的 `sorryAx` 依赖。
- **公理（Axiom）：** 未经库内证明而直接接受的命题，因此属于逻辑信任假设的一部分。
- **三个标准公理：** `propext`、`Classical.choice` 和 `Quot.sound`，即本次审计唯一允许的公理。
- **经内核检查（Kernel-checked）：** 阐释后的证明项已由 Lean 的小型可信内核接受。
- **空真定理（Vacuous theorem）：** 各项假设不可能同时成立，或其结论因意外的平凡原因而为真的定理。
- **孤立模块（Orphan module）：** 无法从库的根导入抵达、因而未包含在根构建中的实际 Lean 源文件。
- **逃生通道（Escape hatch）：** 可绕过常规检查或改变阐释环境的构造或选项。
- **信任路径（Trust path）：** 从源码声明经阐释和公理到内核接受的完整链路。
- **见证（Witness）：** 具名且已编译的具体示例，用以表明假设或定义具有非平凡行为。
- **校准（Calibration）：** 一个特意植入的错误正对照，用以证明扫描器能够检出其目标缺陷。

## 范围与非目标

验证范围是根文件 `MatrixConcentration.lean` 及其导入的全部 14 个扁平模块：一个
Prelude、八个章节和五个附录。共享文件遍历范围包括 Lake 项目根目录下实际存在的每个
`.lean` 文件，仅排除 `.lake/**`、`MatrixConcentration/Verification/**` 和
`.audit_work/**`。测量共发现 15 个文件，15 个全部可从根抵达，没有孤立模块，也没有
范围内的符号链接。两个被排除审计路径下的验证工具和植入对照会单独登记，绝不计入库声明。

本文件夹认证的是证明机制和已声明的信任面，并不独立重做对书籍内容忠实度的检查。
陈述对应关系由[书籍 → Lean 对应表](../README.md)、本地项目附录台账
`../APPENDIX_SUMMARY.md` 以及单独的本地 `TranslationReport/` 审计轨迹负责。这些实时记录
明确将 UP-007 / 书中公式 (6.1.6) 排除在形式化覆盖范围之外。保留的有界结果
`matrix_rosenthal_pinelis_symmetric`、
`matrix_rosenthal_pinelis_centered_with_loss` 及其 `_aux` 辅助项仅作支持用途，
并未登记为该公式的对应端点。许可、版本控制来源、DOI 分配和归档等发布事务也不属于
本轮检查范围。

## 验证索引

| # | 验证项 | 保证内容 | 层级 | 结论 | 发现项（C/M/m/I） | 报告 |
|---|---|---|---|---|---|---|
| V1 | 干净构建完整性 | 在唯一一次获准的干净状态重置后，全部 15 个项目模块均可编译；未出现错误或缺失证明警告。 | 机器 | PASS | 0/0/0/0 | [01_build_integrity.md](01_build_integrity.md) |
| V2 | 导入图完整性 | 每个实际存在的 Lean 源文件都由根构建检查；不存在孤立模块。 | 机器 | PASS-WITH-NOTES | 0/0/0/4 | [02_import_graph.md](02_import_graph.md) |
| V3 | 占位符普查 | 不存在活跃的缺失证明占位符或提前停止标记，且没有声明依赖 `sorryAx`。 | 机器 | PASS | 0/0/0/0 | [03_sorry_audit.md](03_sorry_audit.md) |
| V4 | 通用公理审计 | 每个已加载的项目声明至多使用三个获准的逻辑公理。 | 机器 | PASS | 0/0/0/0 | [04_axiom_audit.md](04_axiom_audit.md) |
| V5 | 逃生通道扫描 | 没有源码构造绕过检查或改变阐释环境；无害选项和局部实例均已登记。 | 混合（机器扫描；人工审查分类） | PASS-WITH-NOTES | 0/0/0/4 | [05_escape_hatches.md](05_escape_hatches.md) |
| V6 | 空真性与平凡性 | 全部 467 个端点均已分类：433 个 OK、34 个 SUSPECT、0 个 VACUOUS。C 层共有 74 个已接受条目：40 个抽样 OK 项加 34 个边界义务，分别通过 54 处库内引用和 20 个具名应用解除。 | 混合（机器完成 A/C 层；人工审查 B 层） | PASS-WITH-NOTES | 0/0/0/3 | [06_vacuity_triviality.md](06_vacuity_triviality.md) |
| V7 | 定义健全性 | 全部 51/51 个被测承重定义都有实质性证据（32 个直接引用条目和 19 个有编译见证支撑的条目）；另披露 78 个零引用叶节点（76 个公开、2 个私有）。 | 混合（机器生成清单/见证；人工审查健全性判断） | PASS-WITH-NOTES | 0/0/0/1 | [07_definition_sanity.md](07_definition_sanity.md) |
| V8 | Linter 与警告检查 | 包级 lint 检查无问题；全新构建产生的每条警告均被归类为维护问题，而非证明不健全。 | 机器 | PASS-WITH-NOTES | 0/0/1/1 | [08_linter_report.md](08_linter_report.md) |
| V9 | 已发布声明交叉检查 | 工具链、计数、端点身份、角色、公理、命令、干净程度和附录状态均与测量结果一致。 | 混合（机器检查声明；人工审查记录时序） | PASS-WITH-NOTES | 0/0/0/1 | [09_readme_claims.md](09_readme_claims.md) |
| V10 | 条件接口普查 | 没有已发布结果依赖未披露、从未解除的原则；三个未发布的条件辅助项已明确披露。 | 混合（机器普查；人工审查裁定） | PASS-WITH-NOTES | 0/0/0/1 | [10_conditional_interfaces.md](10_conditional_interfaces.md) |

`C/M/m/I` 表示 CRITICAL / MAJOR / MINOR / INFO。混合结论结合了机器证据与明确指出的
人工审查判断，并不作为纯自动化保证呈现。

## 声明登记表

| 已发布或记录层面的声明 | 当前测量结果 | 状态 | 证据 |
|---|---|---|---|
| 本库可从干净的项目状态成功构建。 | Recovery-v7 在此前不存在的预留构建目录中构建了全部 15 个模块：3,209 个作业、15 个 `Built`、0 个 `Replayed`、1,196 条已分类警告，没有错误或缺失证明警告，退出码为 0。规范重放覆盖全部 15 个模块，0 个 `Built`、14 个 `Replayed`，退出码为 0。 | CONFIRMED | V1 |
| 根文件覆盖全部 14 个内部模块。 | 15 文件的实际范围中，15/15 均可从根抵达，无孤立模块或源码符号链接。 | CONFIRMED | V2 |
| 不存在 `sorry`、`admit` 或未完成证明。 | 经校准的文本与构建日志扫描未发现生产源码占位符；通用公理普查未发现 `sorryAx`。 | CONFIRMED | V1、V3、V4 |
| 不存在 `native_decide`、自定义公理或检查绕过。 | 经校准的实际源码扫描未发现绕过机制，当前环境中的全部 2,213 个声明均未超出允许的公理集合。 | CONFIRMED | V4、V5 |
| 已审计端点恰好使用三个标准公理。 | 全部 467 个已登记对应端点均独立报告恰好使用 `propext`、`Classical.choice` 和 `Quot.sound`。 | CONFIRMED | V4、V9 |
| 公开声明计数为 467 个 theorem、841 个 lemma 和 135 个 definition，共 1,443 个。 | 可识别注释/字符串的源码重新计数复现了每个数字；另有 82 个私有声明，完整实测源码清单共 1,525 项。 | CONFIRMED | V7、V9 |
| 对应表有 467 行，各章节数量向量为 21/136/35/55/71/62/63/24。 | 提取过程复现了总数和每章计数；名称、模块和角色后缀 467/467 全部一致。 | CONFIRMED | V6、V9 |
| 已登记端点不是空真的，承重定义也不是空壳。 | 独立 V6 将全部 467 个端点分类为 433 个 OK、34 个 SUSPECT 和 0 个 VACUOUS。其 74 个 C 层条目由 40 个抽样项和 34 个边界义务构成，并有 54 处库内引用和 20 个具名应用。独立 V7 以 32 个引用和 19 个见证覆盖全部 51 个承重定义，并记录 78 个无引用叶节点（76 个公开、2 个私有）。 | CONFIRMED | V6、V7 |
| 没有已发布结果依赖未披露、从未解除的原则。 | V10 将 2,213/2,213 个环境常量与 V4 对齐；把 1,526 个文本声明解析为 1,531 个有源码支撑的角色；测得 3,827 个有源码支撑的定理 Prop 绑定项、542 个规范化哈希、368 个人工哈希以及 4,762 个定理实例绑定项；并将 14 个谓词分类为 7 个 PROVED、6 个 CONSUMED-ONLY 和 1 个 DEAD，队列为空。 | CONFIRMED | V10 |
| 附录项目 UP-001 至 UP-006 及 UP-008 有已登记的形式化覆盖；UP-007 / (6.1.6) 是唯一明确声明的例外。 | 字面上的 UP-007 公式没有已登记的 Lean 对应项。保留的有界对称/带损失中心化结果及 `_aux` 辅助项仅作支持用途，不构成对应关系。 | CONFIRMED | V1、V4、V9、V10 |
| 记录中的工具链为 Lean/Mathlib v4.31.0。 | `lean-toolchain`、Lake、当前 Lean 二进制文件和 Mathlib 清单固定版本彼此一致。 | CONFIRMED | V9 |
| README 命令从 Lake 项目根目录运行。 | 两条原样列出的命令均在该目录以退出码 0 完成，并按预期的负对照设计，在先前的源码目录工作路径下执行失败。 | CONFIRMED | V9 |
| 单独的 TranslationReport 轨迹目前不存在未解决的状态不一致。 | 已对 63 份 Markdown 记录作时序检查；历史上的开放条目均由后续关闭记录取代。 | CONFIRMED | V9 |

## 发现项摘要

共记录 16 个发现项：0 个 CRITICAL、0 个 MAJOR、1 个 MINOR、15 个 INFO。
其中没有尚未解决且已确认的证明健全性缺陷。

| 发现项 | 严重程度 | 单行摘要 |
|---|---|---|
| V8-F2 | MINOR | [REVISED](08_linter_report.md)：recovery-v7 含 1,196 条已分类构建警告——813 条维护类和 383 条风格类——但没有错误、缺失证明或已证实的健全性缺陷。 |
| V2-F1 | INFO | [报告](02_import_graph.md#v2-f1--info--stale-parent-scaffold-exists)：规范项目根目录之外存在一个陈旧的并行脚手架，已明确排除。 |
| V2-F2 | INFO | [报告](02_import_graph.md#v2-f2--info--sibling-name-collisions-are-excluded)：同级目录目前含 10 个扁平 Lean 文件，不含顶层 `Pre_MatrixConcentration/` 或 `MatrixConcentration.lean`，另有两个各自限定作用域的 Prelude 名称冲突；它们均不进入本次审计。 |
| V2-F3 | INFO | [报告](02_import_graph.md#v2-f3--info--project-root-readme-is-template-boilerplate)：项目根目录 README 是仓库模板样板，并非库声明的来源。 |
| V2-F4 | INFO | [报告](02_import_graph.md#v2-f4--info--audit-scratch-is-intentionally-excluded)：已列举的植入项和审计暂存内容有意排除在库计数之外。 |
| V5-F1 | INFO | [报告](05_escape_hatches.md#v5-f1--info--benign-source-options-are-inventoried)：150 个源码选项均为资源预算或 linter 设置，没有任何一个禁用检查。 |
| V5-F2 | INFO | [报告](05_escape_hatches.md#v5-f2--info--two-narrow-reducibility-annotations)：两个透明范数别名带有局部可归约性标注，但不会改变信任路径。 |
| V5-F3 | INFO | [报告](05_escape_hatches.md#v5-f3--info--proof-local-instances-and-one-proved-fact)：已审查 75 个证明局部实例和一个经证明的算术 `Fact`。 |
| V5-F4 | INFO | [报告](05_escape_hatches.md#v5-f4--info--auto-implicit-binding-remains-enabled)：默认自动隐式绑定仍处于启用状态；经校准的 V6 扫描未发现可疑的 Type/Prop 自动绑定。 |
| V6-F1 | INFO | [REJECTED](06_vacuity_triviality.md#v6-f1--info--rejected-maxsummandsq-boundary-is-outside-every-in-scope-use)：无界无限族的 `maxSummandSq` 后备情形不在全部 27 个已编译直接使用者的适用范围内，其中包括全部 24 个手写定理使用者。 |
| V6-F2 | INFO | [REJECTED](06_vacuity_triviality.md#v6-f2--info--rejected-gchernoff-zero-boundary-is-avoided-or-neutralized)：每个源码使用者都避开或消除了 `gChernoff` 的零尺度边界。 |
| V6-F3 | INFO | [报告](06_vacuity_triviality.md#v6-f3--info--other-totalized-semantic-boundaries-are-explicit-review-observations)：另外 32 个显式全定义化语义边界都有获接受的非退化证据。 |
| V7-F1 | INFO | [报告](07_definition_sanity.md#v7-f1--info--source-declarations-with-no-source-level-referrer)：修正后的清单有 78 个零引用叶节点，包括 76 个公开声明和 2 个私有声明。 |
| V8-F1 | INFO | [FIXED](08_linter_report.md)：已解决 5 个文档/未使用参数维护问题；全新的包级 lint 检查在 2,213 个声明（1,449 个具名声明、764 个生成声明）和 16 个 linter 上均无问题。 |
| V9-F1 | INFO | [FIXED](09_readme_claims.md#v9-f1--info--fixed-readme-now-names-the-lake-project-root)：源码 README 现已写明正确的 Lake 项目根目录，两条列出的命令均可在那里通过。 |
| V10-F1 | INFO | [KNOWN-LEDGERED / REJECTED，不视为新的健全性缺陷](10_conditional_interfaces.md#v10-f1--info--known-ledgered-rejected-as-a-new-soundness-defect)：三个从未实例化的 NC-Khintchine/bootstrap 辅助项只出现在已明确披露、未发布的条件基础设施中，无需修正。 |

## 如何重新运行

请从 Lake 项目根目录运行。直接调用是安全的快速恢复模式：

```sh
bash MatrixConcentration/Verification/scripts/run_all.sh
bash MatrixConcentration/Verification/scripts/run_all.sh --resume
```

两种形式都会追加写入 `logs/run_all.log`，并跳过已有完成标记
`.audit_work/run_all_stages/*.done` 的编号阶段。它们用于恢复同一次未发生更改但被中断的运行，
不用于认证。

重新认证需要运行：

```sh
bash MatrixConcentration/Verification/scripts/v1_recovery_clean_build.sh
bash MatrixConcentration/Verification/scripts/run_all.sh --fresh
```

`--fresh` 会清除全部 21 个编号阶段标记，以及与摘要绑定的规范重放标记
`.audit_work/v1_clean_build.done`。它不会清除单独的
`.audit_work/v1_recovery_build.done`：运行器要么在此前不存在的指定构建目录中建立
干净证据，要么先验证现有源码/输入摘要、运行器/配置哈希、构建日志哈希、未变更的规范树清单
以及恢复树清单，再复用现有证据。随后，它会重新执行规范重放以及 V1–V5、V8、V9 的机器
检查和 V10 的机器普查。当前 V1 运行器不包含递归删除，也绝不会删除 `.lake/build`；
`.lake/packages` 和 `.lake/config` 同样永远不会被删除。接着，本轮运行会刷新 V2，执行
十份报告的一致性检查，复查两个清单，并写入权威的
[`logs/run_all.log`](logs/run_all.log) 和
[`logs/run_all_status.log`](logs/run_all_status.log)。聚合检查耗时取决于主机负载。
获接受的全新聚合运行（运行 ID `8212cc84-aad8-4abc-b0df-b68fd3241112`）从
`2026-07-20T17:28:34Z` 到 `2026-07-20T17:43:35Z`，历时 901 秒并通过，记录
23 个 `START`、23 个 `PASS`、0 个 `SKIP`、0 个 `FAIL`，最终状态为
`ALL MACHINE STAGES PASSED`。

聚合检查会保留而非重新生成人工审查层面的判断：V6 B 层、V7 健全性裁定以及 V10
语义裁定。可使用以下命令检查其机器前置条件和整理后的台账：

```sh
bash MatrixConcentration/Verification/scripts/v6_run.sh
bash MatrixConcentration/Verification/scripts/v7_run.sh
bash MatrixConcentration/Verification/scripts/v10_run.sh
python3 MatrixConcentration/Verification/scripts/check_consistency.py
python3 MatrixConcentration/Verification/scripts/check_final_lifecycle.py
```

当前与源码绑定的序列已完成 recovery-v7、全新聚合检查，以及独立 V6、V7、V10 重跑。
Recovery-v7 用时 1,148 秒并通过；聚合检查用时 901 秒并通过；独立 V6、V7、V10
分别用时 2,518、240 和 143 秒并通过。

聚合运行器以及独立 V1、V6、V7、V10 运行器都会获取共享的、与能力绑定的原子验证写入锁。
当 V1 或 V10 在 `run_all.sh` 内调用时，它会验证并复用编排器的外层锁，而不是再次获取锁。
最终化保护会在最终证据序列冻结期间阻止未经授权的写入者启动。

每份编号报告都列出了更具体的命令、正对照、预期输出和局限。直接使用 `lake env lean`
运行的测试工具会传入 `-DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false`，因为该命令
不会继承 lakefile 中的 Lean 选项。生命周期检查器是运行后的最终关卡：仅应在明确执行完
全新聚合检查、独立 V6/V7/V10 重跑以及最终记录一致性刷新之后调用。上述前置条件和最终
生命周期检查均已完成；[`logs/final_lifecycle_check.txt`](logs/final_lifecycle_check.txt)
记录了 `problems=0`、`result=PASS`、最终声明清单 14/14 PASS，以及写入锁/最终化保护
检查结果为空；文件同时说明，证书有效要求二者保持不存在。生命周期时序记录区分了
7 月 17 日的历史基线删除操作与 2026 年 7 月 20 日 02:49:53 EDT 的唯一一次重新认证
删除操作。历史 recovery-v6 隔离式干净构建及其验证没有执行删除；该证据链已被取代。
替代它的 recovery-v7 运行和规范重放均已通过，且未删除 `.lake/build`。
仅当写入锁和最终化保护均不存在时，PASS 证书才有效。

## 环境快照

| 项目 | 记录值 |
|---|---|
| 重新认证日期 | 2026 年 7 月 19–20 日（EDT；日志保留 UTC 时间戳） |
| 规范根目录 | Lake 项目根目录（包含 `lakefile.toml` 的仓库目录） |
| Lean / Lake | Lean 4.31.0（`68218e876d2a38b1985b8590fff244a83c321783`），Lake 5.0.0 |
| Mathlib | `inputRev = v4.31.0`，解析后的版本 `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` |
| 主机 | macOS 15.6、Apple M2 Pro（12 核）、16 GB 内存 |
| 已验证源码 | 15 个 Lean 文件；20 个由清单固定的源码/元数据/声明输入 |
| 源码清单顶层 SHA-256 | `38ffff697ae0a6f1529b469255c07e003a7ba30d8097c412c04897747c819c89` |
| 验证输入清单 | 147 个脚本/整理数据/只读台账输入；SHA-256 `119519fe481a288d3ebe9157faff8bc14007fe887396235a63a29887f1b256cf` |
| Recovery-v7 | PASS，运行 ID `d854807a-23cd-4b3f-81f9-310c36ee9e19`，`2026-07-20T17:08:56Z`–`2026-07-20T17:28:04Z`，1,148 秒；3,209 个作业、15 个 `Built`、0 个 `Replayed`、1,196 条警告；日志 SHA-256 `9e25991ff6b5ba971442150cc369ce5d9ef24a2e726f36155435b318116d694f` |
| 全新聚合检查 | PASS，运行 ID `8212cc84-aad8-4abc-b0df-b68fd3241112`，`2026-07-20T17:28:34Z`–`2026-07-20T17:43:35Z`，901 秒；日志 SHA-256 `81b8bb7fa4f415ba1f98e4f5d143390c697bce5e9474ba2464e7a39e303c30b8` |
| 独立 V6 | PASS，运行 ID `06bd42c9-8921-496e-9029-8abd8ef5c141`，`2026-07-20T17:43:57Z`–`2026-07-20T18:25:55Z`，2,518 秒；日志 SHA-256 `3314e0966da5ee4c972281e5e8f072fcbe5ba5628bea50dc623b3d985daa9f09` |
| 独立 V7 | PASS，运行 ID `ea099f89-3c20-466b-bbfb-a4e7abd839f5`，`2026-07-20T18:26:10Z`–`2026-07-20T18:30:10Z`，240 秒；51/51 已覆盖（32 个引用 + 19 个见证），78 个无引用叶节点；日志 SHA-256 `1d8ab2977e077100389e2283fd79fd1abfb5f1203e8c67c3cd2814b31518b497` |
| 独立 V10 | PASS，独立父运行 ID `4501a473-f8a5-49cc-93f7-6b57fe1e3fb3`，`2026-07-20T18:30:27Z`–`2026-07-20T18:32:50Z`，143 秒；日志 SHA-256 `afcfaa944f9336545621fbeb99d9008a16182495f37a9a62aefc8c28b6199adb` |
| 最终生命周期/报告关卡 | PASS：`problems=0`、`result=PASS`、最终声明 14/14 PASS，且写入锁/最终化保护不存在；证书有效要求二者保持不存在 |
| 依赖模式 | 保留 `.lake/packages`；Mathlib olean 文件由 `lake exe cache get` 提供，未从源码重新构建 |

详细环境记录见 [`logs/environment.txt`](logs/environment.txt)，各输入哈希见
[`logs/source_manifest.txt`](logs/source_manifest.txt)，最终跨报告状态见
[`logs/consistency_check.txt`](logs/consistency_check.txt)。独立的最终生命周期关卡已通过，
结果记录于 [`logs/final_lifecycle_check.txt`](logs/final_lifecycle_check.txt)。
