# 🖥️ Multi-Cycle Processor (Custom ISA in Verilog)

A Verilog implementation of a **multi-cycle CPU** designed as part of the *Computer Architecture II* course at Birzeit University.  
This project was developed collaboratively with **[Saja Shareef](#)** and **[Shereen Ibdah](#)**.

---

## 🚀 Project Overview
The project implements a **multi-cycle processor** based on a **custom instruction set architecture (ISA)**.  
Unlike a single-cycle processor, which executes every instruction in one clock cycle, this design splits execution into **multiple stages**, allowing efficient **reuse of hardware components** and a more optimized control structure.

### 🔑 Key Features
- **Custom ISA**: Designed and implemented a tailored instruction set to support basic computation and memory operations.
- **Multi-Cycle Execution**: Instructions executed across stages:
  1. **Instruction Fetch (IF)**
  2. **Instruction Decode (ID)**
  3. **Execution (EX)**
  4. **Memory Access (MEM)**
  5. **Write Back (WB)**
- **Finite State Machine (FSM)**: Control logic designed as an FSM to sequence instruction stages.
- **Hardware Reuse**: Single ALU and unified instruction/data memory reused across stages.
- **Modular Design**: Processor components implemented as Verilog modules (e.g., ALU, register file, memory, control unit).

---

## ⚙️ How It Works
1. **Instruction Fetch**: Load instruction from memory.  
2. **Decode & Register Read**: Identify operation and operands.  
3. **Execute**: Perform ALU operation or compute address.  
4. **Memory Access**: Read/write from memory (if required).  
5. **Write Back**: Store result into the register file.  

The **FSM** ensures each stage is executed in sequence across multiple cycles, optimizing hardware utilization.

---

## 🛠️ Technologies Used
- **Verilog HDL** – for hardware description and simulation
- **ModelSim / Quartus (or similar tools)** – for compiling, simulating, and testing

---

## 👥 Contributors
* [Hamza Awashra](https://github.com/hawashra)
* [Saja Shareef](https://github.com/SajaShareef)
* [Shereen Ibdah](https://github.com/shereenIbdah)

---

## 📖 References
- *Computer Organization and Design: The Hardware/Software Interface* – David A. Patterson & John L. Hennessy  
- [Multi-Cycle Datapath (IC London notes)](https://www.doc.ic.ac.uk/~wl/teachlocal/arch/HP05/multi-cycle-datapath.pdf)

---

## 📌 Notes
This project was developed as an **academic exercise** to demonstrate understanding of CPU datapath design, instruction set design, and hardware description using Verilog.

