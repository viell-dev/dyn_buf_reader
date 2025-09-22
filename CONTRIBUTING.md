# Contributing to Project Name

Thank you for your interest in contributing! This document outlines the process for contributing to this project.

## Getting Started

1. Fork the repository
2. Clone your fork:
   ```bash
   git clone https://github.com/username/project
   cd project
   ```
3. Install recommended VS Code extensions (they will be suggested automatically)
4. Build the project:
   ```bash
   cargo build
   ```

## Development Process

1. Create a new branch:

   ```bash
   git checkout -b feature/name
   ```

2. Make your changes

   - Follow Rust style guidelines
   - Add tests for new functionality
   - Run `cargo clippy` to check for common mistakes
   - Format your code with `cargo fmt`

3. Commit your changes:

   ```bash
   git commit -m "add new feature"
   ```

4. Push to your fork:

   ```bash
   git push origin feature/name
   ```

5. Open a Pull Request

## Pull Request Process

1. Update the README.md with details of changes if needed
2. Update the CHANGELOG.md following the Keep a Changelog format
3. The PR will be merged once you have the sign-off of at least one maintainer

## Running Tests

```bash
cargo test
```

## Code Style

This project uses:

- rustfmt for code formatting
- clippy for linting with additional lints enabled

## Questions?

Feel free to open an issue for any questions or concerns.
