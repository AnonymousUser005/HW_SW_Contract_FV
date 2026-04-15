# TEE Verification Framework

This repository provides **formal modeling and security property verification** of **VM-based Trusted Execution Environments (TEEs)** using [Rosette](https://emina.github.io/rosette/). We build design abstractions for TEEs and use symbolic execution to verify **confidentiality** and **integrity** guarantees of VM-based TEEs.

### ✨ Key Features

- Design- and property- based abstraction of **Intel TDX** and **AMD SEV** from Specification
- Tests to ensure the correctness of model through abstract refinement
- Generating Confidentiality and Integrity properties from Specification
- Symbolic execution using Rosette to verify properties.
- Unified testbench with traceable property failures

---

## 🧠 What are TEEs?

**Trusted Execution Environments (TEEs)** provide isolated environments for executing sensitive code and protecting data, even in the presence of advanced attacker.

### VM-based TEEs

VM-based TEEs integrate hardware-based protections into virtual machines. Unlike enclave-based TEEs (e.g., Intel SGX), they operate at the VM level and protect:

- Memory encryption and integrity
- Guest state and register isolation
- Confidentiality of guest secrets even from hypervisors

Intel TDX and AMD SEV are the state-of-the-art most popular commercially used VM-based TEEs.

---

## 📌 Why security guarantees matter

Modern cloud platforms often colocate VMs from different tenants on shared infrastructure. Without proper isolation, a compromised hypervisor could:

- Access or modify guest memory
- Reuse stale secrets
- Intercept registers or migration data

Hence, **formal verification** ensures these attacks are provably prevented under the TEE design.

---

## 🧩 What’s modeled in this repo?

We model guest lifecycle and relavent data structures of AMD-SEV and trust-domain lifecycle and relavent data structures of Intel-TDX. The specific details can be found in each sub directory.

---

## 📂 Repository Structure

```bash
TEE/
├── sev/                         # AMD SEV verification suite
│   ├── doc/                     # Documentation
│   └── src/                     # Rosette models and properties
│       ├── abi.rkt              # SEV lifecycle ABI
│       ├── common.rkt           # Shared utilities
│       ├── confidentility.rkt   # Confidentiality property checks
│       ├── tables.rkt           # All key SEV data structures
│       └── test.rkt             # Unit tests for SEV
│
├── tdx/                         # Intel TDX verification suite
│   ├── doc/                     # Documentation
│   └── src/                     # TDX symbolic model and properties
│       ├── memory.rkt           # Memory model for TDX
│       ├── instance1.rkt        # Sample instantiation
│       ├── tables.rkt           # All key TDX data structures
│       └── test.rkt             # Unit tests for TDX
│
├── util/
│   └── docker/                  # Docker environment setup
│       └── Dockerfile
│
├── LICENSE
├── README.md
```
---

## 🐳 Setting up with Docker and How to run (Recommended)

We recommend you to run using docker, alternatively you can install relavent dependancies and run on host machine itself.

### 🔧 Build the Docker image

From the `util/docker/` directory:

```bash
docker build -t rosset:1.0.0 .
```

### 🚀 Run inside a container

Map your local model folder into `/formal` and start an interactive session:

```bash
docker run --volume=/path_to_model:/formal -it rosset:1.0.0
```

Once inside, run the relavent files (more details on what to run can be found in each sub-dir):

```bash
racket tables.rkt
```

or run any of the symbolic property checkers:

```bash
racket confidentility.rkt
```

---

## 📚 References

- **AMD SEV**: [AMD Secure Encrypted Virtualization (SEV) Specification](https://www.amd.com/en/developer/sev.html)
- **Intel TDX**: [Intel® Trust Domain Extensions Specification](https://www.intel.com/content/www/us/en/developer/tools/trust-domain-extensions/documentation.html)

---

## 📄 License

MIT License.
