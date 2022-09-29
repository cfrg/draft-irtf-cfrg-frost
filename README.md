# Two-Round Threshold Schnorr Signatures with FROST

This is the working area for the individual Internet-Draft, "Two-Round Threshold Schnorr Signatures with FROST".

* [Editor's Copy](https://cfrg.github.io/draft-irtf-cfrg-frost/#go.draft-irtf-cfrg-frost.html)
* [Datatracker Page](https://datatracker.ietf.org/doc/draft-irtf-cfrg-frost)
* [Individual Draft](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-frost)
* [Compare Editor's Copy to Individual Draft](https://cfrg.github.io/draft-irtf-cfrg-frost/#go.draft-irtf-cfrg-frost.diff)

# Existing implementations

| Implementation                                                             | Language | Ciphersuites                   | Version |
| -------------------------------------------------------------------------- | :------- | :------------------------------| :------ |
| [Reference](https://github.com/cfrg/draft-irtf-cfrg-frost/tree/master/poc) | Sage     | All                            | main    |
| [frost-ristretto255](https://github.com/ZcashFoundation/frost/tree/main/frost-ristretto255) | Rust     | FROST(ristretto255, SHA-512)                            | 04   |
| [frost-p256](https://github.com/ZcashFoundation/frost/tree/main/frost-p256) | Rust     | FROST(P-256, SHA-256)                            | 04   |
| [ecc](https://github.com/aldenml/ecc)                                      | C        | FROST(ristretto255, SHA-512)   | 02 |
| [modular-frost](https://github.com/serai-dex/serai/tree/develop/crypto/frost) | Rust     | All   | 10 |
| [crrl](https://github.com/pornin/crrl/blob/main/src/frost.rs)               | Rust     | All except FROST(Ed448, SHAKE256)    | 08 |

## Contributing

See the
[guidelines for contributions](https://github.com/cfrg/draft-irtf-cfrg-frost/blob/master/CONTRIBUTING.md).

Contributions can be made by creating pull requests.
The GitHub interface supports creating pull requests using the Edit (✏) button.


## Command Line Usage

Formatted text and HTML versions of the draft can be built using `make`.

```sh
$ make
```

Command line usage requires that you have the necessary software installed.  See
[the instructions](https://github.com/martinthomson/i-d-template/blob/main/doc/SETUP.md).

