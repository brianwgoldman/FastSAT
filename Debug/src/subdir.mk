################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables 
CPP_SRCS += \
../src/DNF.cpp \
../src/Decomposition.cpp \
../src/Knowledge.cpp \
../src/Problem.cpp \
../src/main.cpp 

OBJS += \
./src/DNF.o \
./src/Decomposition.o \
./src/Knowledge.o \
./src/Problem.o \
./src/main.o 

CPP_DEPS += \
./src/DNF.d \
./src/Decomposition.d \
./src/Knowledge.d \
./src/Problem.d \
./src/main.d 


# Each subdirectory must supply rules for building sources it contributes
src/%.o: ../src/%.cpp
	@echo 'Building file: $<'
	@echo 'Invoking: Cross G++ Compiler'
	g++ -std=c++11 -O0 -g3 -pg -pedantic -Wall -c -fmessage-length=0 -MMD -MP -MF"$(@:%.o=%.d)" -MT"$(@:%.o=%.d)" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


