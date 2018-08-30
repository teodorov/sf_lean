inductive Object.
inductive Expression.
structure EventDefinition := (name: string).


structure LoopCharacteristics := (name: string).

structure StandardLoopCharacteristics extends LoopCharacteristics :=
    (loopCondition: Expression)
    (loopMaximum: ℕ)
    (testBefore: bool)
.
inductive Rendering.
structure Resource :=
    (name: string).
structure ResourceRole :=
    (resourceRef: Resource)
    (resourceAssignmentExpression: Expression)
.
structure Import :=
    (importType: string)
    (location: string)
    (namespaceX: string)
.
structure ItemDefinition :=
    (isCollection: bool)
    (structureRef: option Object)
    (importX: option Import)
.
structure ItemAwareElement :=
    (itemSubjectRef: ItemDefinition)
.
structure DataInput extends ItemAwareElement.
structure DataOutput extends ItemAwareElement.
structure DataObject extends ItemAwareElement.

structure MultiInstanceLoopCharacteristics extends LoopCharacteristics := 
    (isSequential: bool) 
    (loopDataInputRef: ItemAwareElement)
    (inputDataItem: DataInput)
.

structure InputOutputSpecification :=
    (dataInputs: DataInput)
    (dataOutputs: DataOutput)
.

structure Message :=
    (name: string)
    (itemRef: ItemDefinition)
.


structure Error :=
    (name: string)
    (errorCode: string)
    (structureRef: ItemDefinition)
.
structure Operation :=
    (name: string)
    (inMessageRef: Message)
    (outMessageRef: Message)
    (errorRefs: list Error)
.

structure Assignment :=
    (fromX: Expression)
    (toX: Expression)
.
structure MessageEventDefinition extends EventDefinition :=
    (messageRef: Message)
    (operationRef: Operation)
.
structure TerminateEventDefinition extends EventDefinition.
structure TimerEventDefinition  extends EventDefinition :=
    (timeDate: Expression)
    (timeDuration: Expression)
    (timeCycle: Expression)
.

inductive GatewayDirection
| converging
| diverging
.

structure FlowElement :=
    (name: string)
.
structure FlowNode extends FlowElement.

structure Activity extends FlowNode :=
    (isForComposation: bool)
    (startQuantity: ℕ)
    (completionQuantity: ℕ)
    (loopCharacteristics: option LoopCharacteristics)
    --(default: SequenceFlow)
    (ioSpecification: InputOutputSpecification)
    --(boundaryEventRefs: BoundaryEvent)
.

structure SequenceFlow extends FlowElement :=
    (isImmediate: option bool)
    (sourceRef: FlowNode)
    (targetRef: FlowNode)
    (condition: option Expression)
    (default: Activity)
.

structure Gateway extends FlowNode :=
    (gatewayDirection: GatewayDirection)
.

structure ExclusiveGateway extends Gateway :=
    (default: option SequenceFlow)
.

structure ParallelGateway extends Gateway.
inductive EventBasedGatewayType
| parallel
| exclusive
.
structure EventBasedGateway extends Gateway :=
    (instantiate: bool)
    (eventGatewayType: EventBasedGatewayType)
.

structure DataAssociation :=
    (sourceRef: list ItemAwareElement)
    (targetRef: ItemAwareElement)
    (assignment: Assignment)
.
structure DataOutputAssociation extends DataAssociation.
structure DataInputAssociation extends DataAssociation.

structure Event extends FlowNode.


inductive OutputSet.
structure CatchEvent extends Event :=
    (dataOutputs: list DataOutput)
    (dataOutputAssociation: DataOutputAssociation)
    (outputSet: option OutputSet)
    (eventDefinitions: list EventDefinition)
    (eventDefinitionRefs: list EventDefinition)
.
structure StartEvent extends CatchEvent.

inductive InputSet.
structure ThrowEvent extends Event :=
    (dataInputs: list DataInput)
    (dataInputAssociation: DataInputAssociation)
    (inputSet: option InputSet)
    (eventDefinitions: list EventDefinition)
    (eventDefinitionRefs: list EventDefinition)
.
structure EndEvent extends ThrowEvent.



structure BoundaryEvent extends CatchEvent :=
    (attachedToRef: Activity)
    (cancelActivity: bool)
.

inductive CallableElement.
structure CallActivity extends Activity :=
    (calledElementRef: CallableElement)
.

structure Task extends Activity.
structure ServiceTask extends Task :=
    (implementation: option string)
    (operationRef: Operation)
.
structure UserTask extends Task :=
    (renderings: list Rendering)
    (implementation: option string)
.

structure SubProcess extends Activity :=
    (triggeredByEvent: bool)
    (flowElements: list FlowElement)
.

inductive bpmn_exe
| subProcess (id : ℕ) (name : string) (flowElement : FlowElement) --etc

| textAnnotation (id: ℕ) (text: string)
.

