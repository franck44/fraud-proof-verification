// SPDX-License-Identifier: Apache-2.0

/*
 * Copyright 2022, Specular contributors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *    http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

pragma solidity ^0.8.0;

// import "./OneStepProof.sol";
// import "./VerificationContext.sol";
// import "./Params.sol";

library VerifierHelper {

    struct StateProof {
        bytes32 stackHash; // Commitment of the stack [always]
        
        //  this is not in the original code, but added to avoid having to 
        //  define the stackProof
        bytes32 stackHashAfterPops;
        //  elements to be popped. Only one for POP
        uint256 pops;
    }
    // using VerificationContext for VerificationContext.Context;

    /**
     *  Extract a stack proof from a state proof.
     */
    // function decodeAndVerifyStackProof(
    //     OneStepProof.StateProof memory stateProof,
    //     uint64 popNum, //   value is one for POP
    //     uint64 offset,
    //     bytes calldata encoded
    // ) internal pure returns (uint64, OneStepProof.StackProof memory stackProof) {
    //     // Decode StackProof
    //     (offset, stackProof) = OneStepProof.decodeStackProofForPOP(encoded, offset);
    //     // if (popNum != 0) {
    //         // Reconstruct the stack hash before pops
    //     bytes32 h = stackProof.stackHashAfterPops;
    //     for (uint8 i = uint8(stackProof.pops.length); i > 0; i--) {
    //         h = keccak256(abi.encodePacked(h, stackProof.pops[i - 1]));
    //     }
    //     // Ensure the stack hash reconstructed is the same as the stack hash in stateProof
    //     require(h == stateProof.stackHash, "Bad StackProof");
    //     // } else {
    //     //     // If no pop, the stackHashAfterPops is just the current stack hash
    //     //     stackProof.stackHashAfterPops = stateProof.stackHash;
    //     // }
    //     return (offset, stackProof);
    // }

    /**
     *  
     */
    function decodeAndVerifyStackProofForPOP(
        StateProof memory stateProof //,
        // uint64 popNum, //   value is one for POP
        // uint64 offset,
        // bytes calldata encoded
    ) public pure returns (uint64) {
        // // Decode StackProof
        // uint64 offset;
        // (offset, stackProof) = OneStepProof.decodeStackProofForPOP(stateProof);
        // // if (popNum != 0) {
        //     // Reconstruct the stack hash before pops
        bytes32 h = stateProof.stackHashAfterPops;
        h = keccak256(abi.encodePacked(h, stateProof.pops));
        // for (uint8 i = uint8(stackProof.pops.length); i > 0; i--) {
        //     h = keccak256(abi.encodePacked(h, stackProof.pops[i - 1]));
        // }
        // // Ensure the stack hash reconstructed is the same as the stack hash in stateProof
        require(h == stateProof.stackHash, "Bad StackProof");
        // // } else {
        // //     // If no pop, the stackHashAfterPops is just the current stack hash
        // //     stackProof.stackHashAfterPops = stateProof.stackHash;
        // // }
        // return (offset, stackProof);
        //  does not matter what we return
        return (1);
    }

}